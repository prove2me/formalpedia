-- Prove2me | Theorems.Thm_RiemannVonMangoldt_backlund_bound
-- name    : RiemannVonMangoldt.backlund_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T02:12:12.666873+00:00
-- url     : https://prove2.me/theorems/b57a0922-7548-4177-847f-5ac092893956
-- title:
--   Backlund's explicit bound for $N(T)$, $T>2$
-- statement:
--   Write $N(T)$ for the number of zeros $\rho$ of the Riemann zeta function $\zeta(s)$ with $0<\operatorname{Re}\rho<1$ and $0<\operatorname{Im}\rho\le T$, counted with multiplicity. **Backlund's explicit bound** states that for every real $T>2$,
--   $$\left|N(T)-\left(\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+\frac78\right)\right|<0.137\log T+0.443\log\log T+4.350 .$$
--
--   This makes the error term in the Riemann–von Mangoldt formula fully explicit, with numerical constants, and in particular implies the formula itself.
--
--   **Formalization Note** The source PDF prints the constant inside the bracket as $-\tfrac78$. Backlund's theorem and the standard literature (e.g. Titchmarsh, Ch. 9, and Hasanalizade–Shen–Wong 2022) have $+\tfrac78$, matching the expansion $N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+\frac78+S(T)+O(1/T)$; this draft uses $+\tfrac78$. The decimal constants are exact rationals (`0.137 = 137/1000`, etc.). $N(T)$ is `zetaZeroCount T`.
-- source:
--   Wikipedia, "Riemann–von Mangoldt formula", revision oldid=1362774495 (https://en.wikipedia.org/w/index.php?title=Riemann–von_Mangoldt_formula&oldid=1362774495), displayed formula after "Backlund gives an explicit form of the error for all T > 2" (sign of 7/8 corrected to +7/8). R. J. Backlund, Über die Nullstellen der Riemannschen Zetafunktion, Acta Math. 41 (1918) 345–375.

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts

open Filter Asymptotics Real

namespace RiemannVonMangoldt

theorem backlund_bound (T : ℝ) (hT : 2 < T) :
    |zetaZeroCount T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π) + 7 / 8)| <
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 4.350 := by sorry

end RiemannVonMangoldt
