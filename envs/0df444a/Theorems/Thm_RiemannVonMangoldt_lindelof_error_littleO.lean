-- Prove2me | Theorems.Thm_RiemannVonMangoldt_lindelof_error_littleO
-- name    : RiemannVonMangoldt.lindelof_error_littleO
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T02:12:57.305967+00:00
-- url     : https://prove2.me/theorems/07cbdc2e-72c2-42a5-b6c1-e83767474336
-- title:
--   Under Lindelöf: $N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+o(\log T)$
-- statement:
--   Write $N(T)$ for the number of zeros $\rho$ of the Riemann zeta function $\zeta(s)$ with $0<\operatorname{Re}\rho<1$ and $0<\operatorname{Im}\rho\le T$, counted with multiplicity. Assume the **Lindelöf hypothesis**: $\zeta(\tfrac12+it)=O(t^{\varepsilon})$ as $t\to+\infty$ for every $\varepsilon>0$. Then
--   $$N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+o(\log T)\qquad (T\to\infty).$$
--
--   This is the improvement of the error term in the Riemann–von Mangoldt formula from $O(\log T)$ to $o(\log T)$ conditional on the Lindelöf hypothesis.
--
--   **Formalization Note** The hypothesis is `LindelofHypothesis` and $N(T)$ is `zetaZeroCount T`, both from `Definitions.Def_RiemannVonMangoldt_ZeroCounts`; $o(\log T)$ is Mathlib's `Asymptotics.IsLittleO` along `Filter.atTop`.
-- source:
--   Wikipedia, "Riemann–von Mangoldt formula", revision oldid=1362774495 (https://en.wikipedia.org/w/index.php?title=Riemann–von_Mangoldt_formula&oldid=1362774495), paragraph "Under the Lindelöf and Riemann hypotheses, the error terms can be improved to o(log T) and O(log T / log log T) respectively" (first case). Titchmarsh (1986), Theorem 13.6(A).

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts

open Filter Asymptotics Real

namespace RiemannVonMangoldt

theorem lindelof_error_littleO (hL : LindelofHypothesis) :
    (fun T : ℝ => zetaZeroCount T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π)))
      =o[atTop] Real.log := by sorry

end RiemannVonMangoldt
