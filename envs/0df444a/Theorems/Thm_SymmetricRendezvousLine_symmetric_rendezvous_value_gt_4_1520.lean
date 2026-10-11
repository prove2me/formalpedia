-- Prove2me | Theorems.Thm_SymmetricRendezvousLine_symmetric_rendezvous_value_gt_4_1520
-- name    : SymmetricRendezvousLine.symmetric_rendezvous_value_gt_4_1520
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:54:01.89308+00:00
-- url     : https://prove2.me/theorems/8dde44e0-dcc1-435c-b79a-70c8cc1619a2
-- title:
--   Symmetric rendezvous: $R > 4.1520$
-- statement:
--   **Theorem (Han–Du–Vera–Zuluaga).** The symmetric rendezvous value on the line satisfies
--   $$4.1520<R.$$
--
--   Here $R=\inf_S E(S,S)$ is the symmetric rendezvous value on the line: two players start at distance $2$, each with an independently random unknown orientation, both moving at speed at most $1$, both required to use the same mixed strategy $S$, and $E(S,S)$ is the expected first meeting time (see the definition file).
--
--   Together with the upper bound $R<4.2574$, this localises $R$ to an interval of length about $0.1$ containing the conjectured value $4.25$.
-- source:
--   Open Problem Garden, 'Rendezvous on a line' (posted by mdevos, 2007), http://www.openproblemgarden.org/op/rendezvous_on_a_line ("proving 4.1520 < R < 4.2574"); Q. Han, D. Du, J. C. Vera, L. F. Zuluaga, Improved bounds for the symmetric rendezvous search problem on the line, Operations Research 56(3) (2008).

import Definitions.Def_SymmetricRendezvousLine_defs

namespace SymmetricRendezvousLine

theorem symmetric_rendezvous_value_gt_4_1520 :
    (41520 / 10000 : ENNReal) < symmetricRendezvousValue := by sorry

end SymmetricRendezvousLine
