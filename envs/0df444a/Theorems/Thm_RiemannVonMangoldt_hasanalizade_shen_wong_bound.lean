-- Prove2me | Theorems.Thm_RiemannVonMangoldt_hasanalizade_shen_wong_bound
-- name    : RiemannVonMangoldt.hasanalizade_shen_wong_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T02:12:38.32297+00:00
-- url     : https://prove2.me/theorems/056d97d5-b475-4c7b-a37a-e017edba7c27
-- title:
--   Hasanalizade–Shen–Wong explicit bound for $N(T)$, $T\ge e$
-- statement:
--   Write $N(T)$ for the number of zeros $\rho$ of the Riemann zeta function $\zeta(s)$ with $0<\operatorname{Re}\rho<1$ and $0<\operatorname{Im}\rho\le T$, counted with multiplicity. **Hasanalizade, Shen and Wong** proved that for every real $T\ge e$,
--   $$\left|N(T)-\left(\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}\right)\right|\le 0.1038\log T+0.2573\log\log T+9.3675 .$$
--
--   This explicit form of the Riemann–von Mangoldt formula improves the coefficients of $\log T$ and $\log\log T$ over Backlund's bound and holds from $T=e$ on; it implies the asymptotic formula $N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+O(\log T)$.
--
--   **Formalization Note** The decimal constants are exact rationals. $N(T)$ is `zetaZeroCount T`.
-- source:
--   Wikipedia, "Riemann–von Mangoldt formula", revision oldid=1362774495 (https://en.wikipedia.org/w/index.php?title=Riemann–von_Mangoldt_formula&oldid=1362774495), displayed formula after "This result has since been improved upon, including by E. Hasanalizade, Q. Shen, and P-J. Wong" (for T ≥ e). E. Hasanalizade, Q. Shen, P.-J. Wong, Counting zeros of the Riemann zeta function, J. Number Theory 235 (2022) 219–241, Corollary 1.2, doi:10.1016/j.jnt.2021.06.032.

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts

open Filter Asymptotics Real

namespace RiemannVonMangoldt

theorem hasanalizade_shen_wong_bound (T : ℝ) (hT : Real.exp 1 ≤ T) :
    |zetaZeroCount T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π))| ≤
      0.1038 * Real.log T + 0.2573 * Real.log (Real.log T) + 9.3675 := by sorry

end RiemannVonMangoldt
