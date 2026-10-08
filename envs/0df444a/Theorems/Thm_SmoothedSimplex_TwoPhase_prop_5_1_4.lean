-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_prop_5_1_4
-- name    : SmoothedSimplex.TwoPhase.prop_5_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:29:05.797645+00:00
-- url     : https://prove2.me/theorems/df081cb1-b4fb-468f-8a1c-8e8e2537a7b8
-- title:
--   Proposition 5.1.4 (size of 𝒦)
-- statement:
--   For $n>d\ge3$ and $\sigma>0$, the dyadic scale set $\mathcal K$ in equation (36) satisfies
--   $$|\mathcal K|\le9\log_2\!\left(\frac{nd}{\min(\sigma,1)}\right).$$
--   The bound limits the number of scales summed over in the two phase analyses.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Proposition 5.1.4, printed p. 62, PDF p. 62

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Proposition 5.1.4 (size of 𝒦), printed p. 62, PDF p. 62; 𝒦 is equation (36). Formalization Note: `[n]` is `Fin n`; probability measures use product Gaussian laws. -/
theorem prop_5_1_4 {n d : ℕ} (hn : 3 ≤ d) (hnd : d < n)
    (σ : ℝ) (hσ : 0 < σ) :
    ((kappaGrid n d σ).card : ℝ) ≤
      9 * Real.logb 2 ((n : ℝ) * d / min σ 1) := by sorry

end SmoothedSimplex.TwoPhase
