-- Prove2me | Theorems.Thm_SymmetricRendezvousLine_discrete_symmetric_rendezvous_value_le_seventeen_quarters
-- name    : SymmetricRendezvousLine.discrete_symmetric_rendezvous_value_le_seventeen_quarters
-- status  : Open
-- author  : @SamenHossain
-- created : 2026-10-31T19:09:34.662714+00:00
-- url     : https://prove2.me/theorems/683db2a9-098c-44bb-bafc-0ea06b28d190
-- title:
--   Symmetric rendezvous, discrete model: $R_{\mathrm{disc}} \le 17/4$ (upper half of the HDVZ conjecture)
-- statement:
--   **Conjecture (upper half of Han–Du–Vera–Zuluaga).** In the discrete model of the symmetric rendezvous problem on the line, the value is at most $4.25$:
--   $$R_{\mathrm{disc}}\le\frac{17}{4}.$$
--
--   Here $R_{\mathrm{disc}}$ is the infimum of the expected meeting time $E(S,S)$ over the mixed strategies $S$ all of whose paths are *integer zigzags* (paths starting at $0$ that move at full speed $1$ and change direction only at integer times), both players using the same $S$ with independent randomisations and independent fair-coin orientations, starting at distance $2$ (see the definition file). Equivalently: for every $\varepsilon>0$ there is a single mixed strategy over integer zigzags which, used by both players, has expected meeting time at most $17/4+\varepsilon$.
--
--   Since $R\le R_{\mathrm{disc}}$ trivially, this statement is the upper half $R\le 17/4$ of the conjecture $R=17/4$ (Han, Du, Vera and Zuluaga; Open Problem Garden). All known upper bounds on $R$, including the best proved one $R<4.2574$, come from explicit symmetric strategies of this discrete form, and the conjectured value $4.25$ is the apparent limit of the values of such strategies as their horizon grows. This is an open problem.
--
--   **Formalization Note** Values live in $[0,\infty]$; $17/4$ is the extended-real literal $(17:\overline{\mathbb R}_{\ge0})/4$. The infimum ranges over all mixed strategies supported on integer zigzags, not over a finite grid or horizon.
-- source:
--   Q. Han, D. Du, J. C. Vera, L. F. Zuluaga, Improved bounds for the symmetric rendezvous value on the line, Operations Research 56(3) (2008) 772-782, Abstract (p. 772): "we conjecture that the symmetric rendezvous value is asymptotically equal to 4.25", together with the paper's reduction R = R_disc to integer-time full-speed strategies; Open Problem Garden, 'Rendezvous on a line' (posted by mdevos, 2007), http://www.openproblemgarden.org/op/rendezvous_on_a_line (conjecture R = 4.25). Upper half of the conjecture, stated in the discrete model.

import Definitions.Def_SymmetricRendezvousLine_defs

namespace SymmetricRendezvousLine

theorem discrete_symmetric_rendezvous_value_le_seventeen_quarters :
    discreteSymmetricRendezvousValue ≤ 17 / 4 := by sorry

end SymmetricRendezvousLine
