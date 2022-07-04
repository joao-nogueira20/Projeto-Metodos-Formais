# Projeto-Métodos-Formais


Sistema de Permissões em Arquivos e Diretórios

Um determinado sistema operacional define três níveis de permissão para diretórios e arquivos (objetos): Leitura, Leitura/Escrita e Dono. O dono é o único que pode modificar a permissão de um objeto. Cada uma das seguintes categorias de usuários possui um nível de permissão para cada objeto: Para Todos, Usuários Externos, Usuários deste Computador. Por exemplo, um arquivo file.txt pode ter permissão de dono para Usuários deste Computador, permissão de Leitura/Escrita para usuários Externos, e Leitura Para Todos. Diretórios podem conter outros diretórios e arquivos (a pasta Root é a pasta superior de todas as outras). Naturalmente, um arquivo deve sempre estar contido num diretório. Um arquivo nunca pode ter, para uma determinada categoria de usuários, uma permissão menos restrita do que um diretório ancestral dele.




Elabore um modelo em Alloy para contemplar a especificação acima. Os seguintes requisitos (mínimos) devem ser contemplados e naturalmente o que está especificado deve estar devidamente representado no modelo de vocês:
Definição de 5 predicados e 3 funções
Definição de 5 operações que simulam o comportamento do sistema 
Definição e verificação de 5 asserts (testes sobre o sistema)
