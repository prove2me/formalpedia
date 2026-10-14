-- Prove2me | Theorems.Thm_RiemannVonMangoldt_riemann_hypothesis_error_bigO
-- name    : RiemannVonMangoldt.riemann_hypothesis_error_bigO
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T02:14:24.278545+00:00
-- url     : https://prove2.me/theorems/99402b05-6f32-4433-abcf-e2be6ed98058
-- title:
--   Under RH: $N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+O(\log T/\log\log T)$
-- statement:
--   Write $N(T)$ for the number of zeros $\rho$ of the Riemann zeta function $\zeta(s)$ with $0<\operatorname{Re}\rho<1$ and $0<\operatorname{Im}\rho\le T$, counted with multiplicity. Assume the **Riemann hypothesis**: every nontrivial zero of $\zeta$ has real part $\tfrac12$. Then
--   $$N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+O\!\left(\frac{\log T}{\log\log T}\right)\qquad (T\to\infty).$$
--
--   This is the conditional improvement of the error term in the Riemann–von Mangoldt formula under the Riemann hypothesis.
--
--   **Formalization Note** The hypothesis is Mathlib's `RiemannHypothesis`; $N(T)$ is `zetaZeroCount T`; the $O$ is `Asymptotics.IsBigO` along `Filter.atTop`.
-- source:
--   Wikipedia, "Riemann–von Mangoldt formula", revision oldid=1362774495 (https://en.wikipedia.org/w/index.php?title=Riemann–von_Mangoldt_formula&oldid=1362774495), paragraph "Under the Lindelöf and Riemann hypotheses, the error terms can be improved to o(log T) and O(log T / log log T) respectively" (second case). Titchmarsh (1986), Theorem 14.13.

import Mathlib
import Definitions.Def_RiemannVonMangoldt_ZeroCounts

open Filter Asymptotics Real

namespace RiemannVonMangoldt

theorem riemann_hypothesis_error_bigO (hRH : RiemannHypothesis) :
    (fun T : ℝ => zetaZeroCount T - (T / (2 * π) * Real.log (T / (2 * π)) - T / (2 * π)))
      =O[atTop] (fun T : ℝ => Real.log T / Real.log (Real.log T)) := by sorry

end RiemannVonMangoldt
