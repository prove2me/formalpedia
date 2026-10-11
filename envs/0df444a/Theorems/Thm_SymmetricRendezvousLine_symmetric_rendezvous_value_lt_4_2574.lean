-- Prove2me | Theorems.Thm_SymmetricRendezvousLine_symmetric_rendezvous_value_lt_4_2574
-- name    : SymmetricRendezvousLine.symmetric_rendezvous_value_lt_4_2574
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:54:23.522147+00:00
-- url     : https://prove2.me/theorems/2c7e3d7e-afe2-4911-97f3-57d15fc7c266
-- title:
--   Symmetric rendezvous: $R < 4.2574$
-- statement:
--   **Theorem (Han–Du–Vera–Zuluaga).** The symmetric rendezvous value on the line satisfies
--   $$R<4.2574.$$
--
--   Here $R=\inf_S E(S,S)$ is the symmetric rendezvous value on the line: two players start at distance $2$, each with an independently random unknown orientation, both moving at speed at most $1$, both required to use the same mixed strategy $S$, and $E(S,S)$ is the expected first meeting time (see the definition file).
--
--   Equivalently, some single mixed strategy used by both players achieves expected meeting time below $4.2574$.
-- source:
--   Open Problem Garden, 'Rendezvous on a line' (posted by mdevos, 2007), http://www.openproblemgarden.org/op/rendezvous_on_a_line ("proving 4.1520 < R < 4.2574"); Q. Han, D. Du, J. C. Vera, L. F. Zuluaga, Improved bounds for the symmetric rendezvous search problem on the line, Operations Research 56(3) (2008).

import Definitions.Def_SymmetricRendezvousLine_defs

namespace SymmetricRendezvousLine

theorem symmetric_rendezvous_value_lt_4_2574 :
    symmetricRendezvousValue < (42574 / 10000 : ENNReal) := by sorry

end SymmetricRendezvousLine
