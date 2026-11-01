-- Prove2me | Theorems.Thm_SymmetricRendezvousLine_discrete_symmetric_rendezvous_value_ge_seventeen_quarters
-- name    : SymmetricRendezvousLine.discrete_symmetric_rendezvous_value_ge_seventeen_quarters
-- status  : Open
-- author  : @SamenHossain
-- created : 2026-10-31T19:09:28.726994+00:00
-- url     : https://prove2.me/theorems/a03ad4f2-d64b-4af5-9a6c-60eb2878cd49
-- title:
--   Symmetric rendezvous, discrete model: $17/4 \le R_{\mathrm{disc}}$ (lower half of the HDVZ conjecture)
-- statement:
--   **Conjecture (lower half of Han–Du–Vera–Zuluaga).** In the discrete model of the symmetric rendezvous problem on the line, the value is at least $4.25$:
--   $$\frac{17}{4}\le R_{\mathrm{disc}}.$$
--
--   Here $R_{\mathrm{disc}}$ is the infimum of the expected meeting time $E(S,S)$ over the mixed strategies $S$ all of whose paths are *integer zigzags* (paths starting at $0$ that move at full speed $1$ and change direction only at integer times), both players using the same $S$ with independent randomisations and independent fair-coin orientations, starting at distance $2$ (see the definition file). Equivalently: every mixed strategy over integer zigzags, used by both players, has expected meeting time at least $17/4$.
--
--   Combined with the Han–Du–Vera–Zuluaga reduction $R=R_{\mathrm{disc}}$, this is the lower half $17/4\le R$ of the conjecture $R=17/4$ (Han, Du, Vera and Zuluaga; Open Problem Garden). The best proved lower bound is $4.1520<R$, obtained by Han, Du, Vera and Zuluaga from a finite-horizon relaxation of the discrete problem solved as a semidefinite program; closing the gap to $4.25$ is open.
--
--   **Formalization Note** Values live in $[0,\infty]$; $17/4$ is the extended-real literal $(17:\overline{\mathbb R}_{\ge0})/4$. The infimum ranges over all mixed strategies supported on integer zigzags, including those that delay meeting indefinitely (their expected meeting time may be $\infty$).
-- source:
--   Q. Han, D. Du, J. C. Vera, L. F. Zuluaga, Improved bounds for the symmetric rendezvous value on the line, Operations Research 56(3) (2008) 772-782, Abstract (p. 772): "we conjecture that the symmetric rendezvous value is asymptotically equal to 4.25", together with the paper's reduction R = R_disc to integer-time full-speed strategies and its lower bound 4.1520 < R; Open Problem Garden, 'Rendezvous on a line' (posted by mdevos, 2007), http://www.openproblemgarden.org/op/rendezvous_on_a_line (conjecture R = 4.25). Lower half of the conjecture, stated in the discrete model.

import Definitions.Def_SymmetricRendezvousLine_defs

namespace SymmetricRendezvousLine

theorem discrete_symmetric_rendezvous_value_ge_seventeen_quarters :
    17 / 4 ≤ discreteSymmetricRendezvousValue := by sorry

end SymmetricRendezvousLine
