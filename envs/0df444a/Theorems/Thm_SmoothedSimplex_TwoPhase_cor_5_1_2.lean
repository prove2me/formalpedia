-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_cor_5_1_2
-- name    : SmoothedSimplex.TwoPhase.cor_5_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:28:49.238975+00:00
-- url     : https://prove2.me/theorems/25a8d28f-836f-42a6-af2a-fbc28f3957fe
-- title:
--   Corollary 5.1.2 (probability of small s_min(A_{𝓘(A)}))
-- statement:
--   Under Lemma 5.1.1's Gaussian assumptions, draw $\lceil3nd\ln n\rceil$ independent uniform $d$-subsets and select $\mathcal I(A)$ maximizing $s_{\min}(A_I)$. Then
--   $$\Pr_{A,\mathcal I}\!\left[s_{\min}(A_{\mathcal I(A)})\le\kappa_0\right]\le\frac{0.417}{\binom nd}.$$
--   The result turns the many-good-minors estimate into a guarantee for the selected sampled basis. **Formalization Note** Ties select the first draw.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Corollary 5.1.2, printed p. 60, PDF p. 60

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Corollary 5.1.2 (small s_min at the selected sample), printed p. 60, PDF p. 60. The samples are independent and uniform with replacement; count is rounded upward. Formalization Note: `[n]` is `Fin n`; probability measures use product Gaussian laws. -/
theorem cor_5_1_2 {n d : ℕ} (hn : 3 ≤ d) (hnd : d < n)
    (c : Fin n → Point d) (hc : ∀ i, ‖c i‖ ≤ 1) (σ : ℝ) (hσ : 0 < σ) :
    (((gaussianFamily c σ).prod (sampleLaw n d)) {p |
      sMin p.1 (bestSample p.1 p.2) ≤ kappaZero n d σ}).toReal ≤
        (0.417 : ℝ) / Nat.choose n d := by sorry

end SmoothedSimplex.TwoPhase
