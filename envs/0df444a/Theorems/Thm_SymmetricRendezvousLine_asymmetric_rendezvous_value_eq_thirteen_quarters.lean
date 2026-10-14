-- Prove2me | Theorems.Thm_SymmetricRendezvousLine_asymmetric_rendezvous_value_eq_thirteen_quarters
-- name    : SymmetricRendezvousLine.asymmetric_rendezvous_value_eq_thirteen_quarters
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T09:52:51.766361+00:00
-- url     : https://prove2.me/theorems/847f191c-8acc-4089-871c-44a7abc41ca5
-- title:
--   Asymmetric rendezvous on the line: $R^a = 13/4$ (Alpern–Gal)
-- statement:
--   **Theorem (Alpern–Gal, 1995).** If the two players may use *different* strategies, the infimum expected meeting time is $3.25$:
--   $$R^a=\inf_{S_1,S_2}E(S_1,S_2)=\frac{13}{4}.$$
--
--   Here the setting is the same as for the symmetric problem: players start at distance $2$ (player I at $0$, player II at $2$), each player's forward direction is an independent fair coin, speeds are at most $1$, and $E(S_1,S_2)$ is the expected first meeting time when player I uses $S_1$ and player II uses $S_2$ independently.
--
--   Since every symmetric strategy pair $(S,S)$ is admissible here, $R^a\le R$; this value is the benchmark against which the cost of the symmetry constraint is measured.
-- source:
--   Open Problem Garden, 'Rendezvous on a line' (posted by mdevos, 2007), http://www.openproblemgarden.org/op/rendezvous_on_a_line ("Alpern and Gal [AG] have shown that the inf expected meeting time is 3.25"); S. Alpern, S. Gal, Rendezvous search on the line with distinguishable players, SIAM J. Control Optim. 33(4) (1995) 1270-1276.

import Definitions.Def_SymmetricRendezvousLine_defs

namespace SymmetricRendezvousLine

theorem asymmetric_rendezvous_value_eq_thirteen_quarters :
    asymmetricRendezvousValue = 13 / 4 := by sorry

end SymmetricRendezvousLine
