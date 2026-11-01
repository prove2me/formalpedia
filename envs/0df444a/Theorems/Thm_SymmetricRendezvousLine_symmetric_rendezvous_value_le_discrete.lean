-- Prove2me | Theorems.Thm_SymmetricRendezvousLine_symmetric_rendezvous_value_le_discrete
-- name    : SymmetricRendezvousLine.symmetric_rendezvous_value_le_discrete
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-31T19:09:29.189117+00:00
-- url     : https://prove2.me/theorems/5db6800e-4d6c-43d1-a1b4-03acf328f94d
-- title:
--   Symmetric rendezvous: $R \le R_{\mathrm{disc}}$ (easy half of the HDVZ reduction)
-- statement:
--   The symmetric rendezvous value on the line is at most its discrete counterpart:
--   $$R \le R_{\mathrm{disc}}.$$
--
--   Here $R=\inf_S E(S,S)$ is the infimum of the expected meeting time over *all* mixed strategies $S$ (two players at distance $2$, independent random orientations, speed at most $1$, both using $S$), and $R_{\mathrm{disc}}$ is the infimum of the same quantity $E(S,S)$ over the mixed strategies all of whose paths are *integer zigzags*: paths starting at $0$ that move at full speed $1$ and change direction only at integer times (see the definition file).
--
--   This is the trivial half of the Han–Du–Vera–Zuluaga reduction $R=R_{\mathrm{disc}}$ of the symmetric problem to a discrete one: the strategies admissible in $R_{\mathrm{disc}}$ form a subfamily of those admissible in $R$, so the infimum over the larger family is smaller. The substantive half, $R_{\mathrm{disc}}\le R$, is the dominance statement that integer-time full-speed strategies dominate among all strategies.
--
--   **Formalization Note** Both values live in $[0,\infty]$; the inequality is between the two infima of the definition file.
-- source:
--   Q. Han, D. Du, J. C. Vera, L. F. Zuluaga, Improved bounds for the symmetric rendezvous value on the line, Operations Research 56(3) (2008) 772-782, reduction of the problem to strategies moving at full speed and changing direction only at integer times (trivial inequality R <= R_disc of that reduction); Open Problem Garden, 'Rendezvous on a line' (posted by mdevos, 2007), http://www.openproblemgarden.org/op/rendezvous_on_a_line ("Han, Du, Vera, and Zuluaga [HDVZ] have shown that strategies in which the players move at maximum speed and only change direction at integer times dominate among all possible strategies - thus reducing this problem to a discrete one").

import Definitions.Def_SymmetricRendezvousLine_defs

namespace SymmetricRendezvousLine

theorem symmetric_rendezvous_value_le_discrete :
    symmetricRendezvousValue ≤ discreteSymmetricRendezvousValue := by sorry

end SymmetricRendezvousLine
