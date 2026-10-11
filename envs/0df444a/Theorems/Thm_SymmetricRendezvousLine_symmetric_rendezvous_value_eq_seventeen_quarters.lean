-- Prove2me | Theorems.Thm_SymmetricRendezvousLine_symmetric_rendezvous_value_eq_seventeen_quarters
-- name    : SymmetricRendezvousLine.symmetric_rendezvous_value_eq_seventeen_quarters
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:55:12.335571+00:00
-- url     : https://prove2.me/theorems/60320ddb-c6bd-4f6b-a6cb-d7418b057ca6
-- title:
--   Symmetric rendezvous on the line: $R = 17/4$
-- statement:
--   **Conjecture (Han–Du–Vera–Zuluaga).** The symmetric rendezvous value on the line equals $4.25$:
--   $$R=\frac{17}{4}.$$
--
--   Here $R=\inf_S E(S,S)$ is the symmetric rendezvous value on the line: two players start at distance $2$, each with an independently random unknown orientation, both moving at speed at most $1$, both required to use the same mixed strategy $S$, and $E(S,S)$ is the expected first meeting time (see the definition file).
--
--   This determines the answer to the question posed on the Open Problem Garden: the infimum expected meeting time achievable when both players must adopt the same strategy.
--
--   **Formalization Note** The equality is in $[0,\infty]$; a disproof (showing $R\neq 17/4$) is also a meaningful outcome.
-- source:
--   Open Problem Garden, 'Rendezvous on a line' (posted by mdevos, 2007), http://www.openproblemgarden.org/op/rendezvous_on_a_line; conjecture stated in Q. Han, D. Du, J. C. Vera, L. F. Zuluaga, Improved bounds for the symmetric rendezvous search problem on the line, Operations Research 56(3) (2008).

import Definitions.Def_SymmetricRendezvousLine_defs

namespace SymmetricRendezvousLine

theorem symmetric_rendezvous_value_eq_seventeen_quarters :
    symmetricRendezvousValue = 17 / 4 := by sorry

end SymmetricRendezvousLine
