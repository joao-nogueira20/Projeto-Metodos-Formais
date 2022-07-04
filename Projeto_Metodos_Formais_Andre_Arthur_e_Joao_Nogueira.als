one sig SistemaOperacional {
	root: one Root,
	usuarios: some Usuario
}

abstract sig TipoUsuario{}

one sig UsuarioParaTodos, UsuarioExterno, UsuarioDesteComputador extends TipoUsuario{}

sig Usuario{
tipo:  TipoUsuario
}

abstract sig Permissao{}

one sig PermissaoLeitura, PermissaoLeituraEscrita, PermissaoDono extends Permissao{}

abstract sig Objeto {
	permissoes:  TipoUsuario -> one Permissao
}

abstract sig Diretorio extends Objeto{
	objetos: set Objeto
}

sig Arquivo extends Objeto{
//atributo paiDoArquivo diz quem é o pai do Arquivo
paiDoArquivo: one Diretorio
}

sig DiretorioComum extends Diretorio{
//atributo paiDoDiretorio diz quem é o pai de DiretorioComum
paiDoDiretorio: one Diretorio
}

one sig Root extends Diretorio{}



// Todo objeto deve pertencer a um diretório, exceto quando é um Root.
fact  TodoObjetoNaoRootPertenceUmDiretorio {
	all o: Objeto | (o !in Root) implies (one d: Diretorio | o in d.objetos) else (no d: Diretorio | o in d.objetos)
}

// Todo diretorio não pode ser pai dele mesmo
fact DiretorioNaoEhPaiDeleMesmo{
	all d: Diretorio | d.paiDoDiretorio !=d
}

// Todo DiretorioComum está abaixo da Root
fact DiretorioComumInferiorARoot{
	all d: DiretorioComum | Root in d.^paiDoDiretorio
}

//  Todo DiretorioComum tem que estar nos objetos do seu pai
fact TodoDiretorioComumEstaNosObjetosDoSeuPai{
	all d: DiretorioComum| d in (d.paiDoDiretorio).objetos
}

// Todo Arquivo tem que estar nos objetos de seu pai
fact TodoArquivoEstaNosObjetosDoSeuPai{
	all a: Arquivo | a in (a.paiDoArquivo).objetos 
}

// Todo Arquivo só pode estar em um diretorio
fact ArquivoEmUmUnicoDiretorio{
	all a: Arquivo | one a.~objetos
}

// Todos os usuários pertencem ao sistema operacional
fact UsuariosNoSistemaOperacional {
	all u: Usuario | one s:SistemaOperacional | u in s.usuarios
}

//  Todo diretório não pode conter ele mesmo no seu conjunto de objetos.
fact DiretorioNaoContemNeleMesmo {
	all d:Diretorio | d !in d.^objetos
}

// Todo objeto deve ser filho direta ou indiretamente da root.
fact RootAncestral{
	all o:Objeto | one r: Root | o in r.*objetos
}

// Todo Objeto deve ter pelo menos um tipo de usuário como dono.
fact TodoObjetoTemPeloMenosUmTipoUsuarioComoDono{
	all o:Objeto | one p:PermissaoDono | some u:TipoUsuario | u -> p in o.permissoes
}

// Toda Permissao criada no modelo precisa estar relacionada a um Objeto
fact TodaPermissaoEstaRelacionadaAUmObjeto{
	all p: Permissao | p in Objeto.permissoes[TipoUsuario] 
}

// Todo TipoUsuario criado no modelo precisa estar relacionado a um Usuario
fact{
	all t: TipoUsuario | t in Usuario.tipo
}




// quantos objetos tem em um determinado Diretorio
fun quantidadeObjetosEmUmDiretorio(d: Diretorio): Int {
	#d.objetos
}



//  quais usuários tem uma determinada permissão em um objeto específico
fun UsuariosComPermissaoEspecificaEmUmObjeto(o:Objeto,p:Permissao) : set Usuario{
	tipo.(o.permissoes).p
}



// retorna a permissão que um Usuário tem para determinado Objeto
fun QualPermissaoDoUsuarioNoObjeto(o: Objeto ,u: Usuario): one Permissao {
(o.permissoes)[u.tipo]

}


// checa se o Usuário pertence ao Sistema Operacional
pred UsuarioPertenceAoSistema[ u:Usuario]{
u in SistemaOperacional.usuarios
}


// checa se um arquivo pode ser editado(PermissaoDono ou PermissaoLeituraEscrita) por um usuário
pred ArquivoPodeSerEditadoPorUsuario[a:Arquivo,u:Usuario]{
a.permissoes[u.tipo] = PermissaoDono or a.permissoes[u.tipo] = PermissaoLeituraEscrita
}


// checa se o diretorio está vazio
pred DiretorioEstaVazio [d: Diretorio] {
#d.objetos = 0
}


// Existe algum DiretorioComum dentro de um determinado DiretorioComum
pred DiretorioContemOutroDiretorio [d: Diretorio]{
 d in DiretorioComum.paiDoDiretorio
}


// checa se o arquivo está em um  DiretorioComum específico
pred ArquivoEstaContidoNoDiretorio[a:Arquivo,d:Diretorio]{
a in d.objetos
}



fact ApenasUsuariosComPermissaoDonoAlteramPermissao{
	all o: Objeto, p: Permissao | apenasDonosAlteramPermissao[o, p]
}

pred apenasDonosAlteramPermissao(o: Objeto, p: Permissao) {
	some u: Usuario | buscarPermissaoNoObjeto[o, u] != PermissaoDono implies alterarPermissao[o,u.tipo, p] 
}

pred alterarPermissao(o: Objeto, t: TipoUsuario, p: Permissao) {
	(o.permissoes) = (o.permissoes)++( t -> p)
}

fun buscarPermissaoNoObjeto(o: Objeto, u: Usuario): one Permissao {
	(u.tipo).(o.permissoes)
}



// Um objeto não pode ter uma permissão menos restrita do que um de seus ancestrais
fact GarantirHierarquiaObjetos{
	hierarquiaPermissaoDiretorioComum
	hierarquiaPermissaoArquivo
}

// Um DiretorioComum  não pode ter uma permissão menos restrita do que um de seus ancestrais
pred hierarquiaPermissaoDiretorioComum {
	hierarquiaPermissaoDiretorioComumDono
	hierarquiaPermissaoDiretorioComumLeituraEscrita
}


pred hierarquiaPermissaoDiretorioComumDono{
	no d: DiretorioComum | ~(d.permissoes).UsuarioParaTodos = PermissaoDono and
    (~((d.paiDoDiretorio).permissoes).UsuarioParaTodos = PermissaoLeituraEscrita or 
    ~((d.paiDoDiretorio).permissoes).UsuarioParaTodos = PermissaoLeitura)

	no d: DiretorioComum | ~(d.permissoes).UsuarioExterno = PermissaoDono and
    (~((d.paiDoDiretorio).permissoes).UsuarioExterno = PermissaoLeituraEscrita or 
    ~((d.paiDoDiretorio).permissoes).UsuarioExterno = PermissaoLeitura)

	no d: DiretorioComum | ~(d.permissoes).UsuarioDesteComputador = PermissaoDono and
    (~((d.paiDoDiretorio).permissoes).UsuarioDesteComputador = PermissaoLeituraEscrita or 
    ~((d.paiDoDiretorio).permissoes).UsuarioDesteComputador = PermissaoLeitura)
}

pred hierarquiaPermissaoDiretorioComumLeituraEscrita{
	no d: DiretorioComum | ~(d.permissoes).UsuarioParaTodos = PermissaoLeituraEscrita and
    (~((d.paiDoDiretorio).permissoes).UsuarioParaTodos =  PermissaoLeitura)

	no d: DiretorioComum | ~(d.permissoes).UsuarioExterno = PermissaoLeituraEscrita and
    (~((d.paiDoDiretorio).permissoes).UsuarioExterno =   PermissaoLeitura)

	no d: DiretorioComum | ~(d.permissoes).UsuarioDesteComputador = PermissaoLeituraEscrita and
    (~((d.paiDoDiretorio).permissoes).UsuarioDesteComputador =   PermissaoLeitura)
}

// Um Arquivo não pode ter uma permissão menos restrita do que um de seus ancestrais
pred hierarquiaPermissaoArquivo{
hierarquiaPermissaoArquivoUsuarioParaTodos
hierarquiaPermissaoArquivoUsuarioExterno
hierarquiaPermissaoArquivoUsuarioDesteComputador
}

pred hierarquiaPermissaoArquivoUsuarioParaTodos{
	no a: Arquivo |  ~(a.permissoes).UsuarioParaTodos = PermissaoDono and 
	(~((a.paiDoArquivo).permissoes).UsuarioParaTodos = PermissaoLeituraEscrita or
	~((a.paiDoArquivo).permissoes).UsuarioParaTodos = PermissaoLeitura) 

	no a: Arquivo |  ~(a.permissoes).UsuarioParaTodos =  PermissaoLeituraEscrita and 
	(~((a.paiDoArquivo).permissoes).UsuarioParaTodos = PermissaoLeitura)
}

pred hierarquiaPermissaoArquivoUsuarioExterno{
	no a: Arquivo |  ~(a.permissoes).UsuarioExterno = PermissaoDono and 
	(~((a.paiDoArquivo).permissoes).UsuarioExterno = PermissaoLeituraEscrita or
	~((a.paiDoArquivo).permissoes).UsuarioExterno = PermissaoLeitura) 

	no a: Arquivo |  ~(a.permissoes).UsuarioExterno =  PermissaoLeituraEscrita and 
	(~((a.paiDoArquivo).permissoes).UsuarioExterno = PermissaoLeitura)
}

pred hierarquiaPermissaoArquivoUsuarioDesteComputador{
	no a: Arquivo |  ~(a.permissoes).UsuarioDesteComputador = PermissaoDono and 
	(~((a.paiDoArquivo).permissoes).UsuarioDesteComputador = PermissaoLeituraEscrita or
	~((a.paiDoArquivo).permissoes).UsuarioDesteComputador = PermissaoLeitura) 

	no a: Arquivo |  ~(a.permissoes).UsuarioDesteComputador =  PermissaoLeituraEscrita and 
	(~((a.paiDoArquivo).permissoes).UsuarioDesteComputador = PermissaoLeitura)
}



// adicionar usuário
pred AdicionarUsuario(s,s1: SistemaOperacional,u: Usuario){
s1.usuarios = s.usuarios + u 
}

// remover usuário
pred RemoverUsuario(s,s1: SistemaOperacional,u: Usuario){
s1.usuarios = s.usuarios - u
}


// retorna os ancestrais de um determinado objeto
fun quaisOsAncestrais(o: Objeto): set Diretorio {
	o.^(~objetos)
}




// verifica se todo objeto tem Root como diretorio superior
assert herdeiroDaRoot {
	all o: Objeto - Root | Root in (quaisOsAncestrais[o] )
}



// verifica se um objeto está em mais de 1 diretório ao mesmo tempo
assert verificaObjetoDuplicado {
	no o: Objeto,d1, d2: Diretorio | d1 != d2 and o in d1.objetos and o in d2.objetos
}


// verifica se nenhum diretorio está dentro dele mesmo
assert nenhumDiretorioDentroDeleMesmo{
	no d:Diretorio | d in d.objetos
}


// verifica se nenhum usuario tem PermissaoLeituraEscrita em um arquivo e PermissaoLeitura
// no diretorio pai deste arquivo
assert usuarioNaoTemPermissaoLeituraEscritaNoArquivoEPermissaoLeituraNoDiretorio {
	no a:Arquivo,u:Usuario | u.tipo.(a.permissoes) = PermissaoLeituraEscrita and 
	u.tipo.(a.paiDoArquivo.permissoes) = PermissaoLeitura
}


// verifica se o sistema operacional tem apenas uma root
assert oSistemaOperacionalSoTemUmaRoot{
	all s: SistemaOperacional | #s.root = 1 
}


// todo arquivo está em um único diretorio
assert arquivoEmDiretorio{
	all a: Arquivo| one d: Diretorio | a in d.objetos  
}


pred teste{}

run teste for 6 but exactly 4 Usuario, 1 DiretorioComum
