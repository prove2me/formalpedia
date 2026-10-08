-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_lemma_5_3_1
-- name    : SmoothedSimplex.TwoPhase.lemma_5_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:29:53.145832+00:00
-- url     : https://prove2.me/theorems/4af30046-b23c-4a25-9874-716e61d84823
-- title:
--   Lemma 5.3.1 (LP⁺) — corrected dimension
-- statement:
--   Let $n>d\ge3$, $\max_i\|(\bar y_i,\bar a_i)\|\in(1/2,1]$, and $\sigma>0$. After independent Gaussian perturbation of all LP data, the second-phase shadow count obeys
--   $$\mathbb E S_z^+\le49\log_2\!\frac{nd}{\min(\sigma,1)}\;\mathcal D\!\left(n,d+1,\frac{\min(1,\sigma^5)}{2^{23}(d+1)^{11/2}n^{14}(\ln n)^{5/2}}\right)+n.$$
--   This is the LP⁺ contribution to the main theorem. **Formalization Note** The dimension $d+1$ corrects the paper's printed $d$ for the lifted LP⁺; integrability is asserted in the conclusion.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 5.3.1, printed p. 80, PDF p. 80

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Lemma 5.3.1 (LP⁺), printed p. 80, PDF p. 80. Corrected D’s dimension to d+1 because LP⁺ lives in ℝ^(d+1); the proof uses this dimension. Formalization Note: `[n]` is `Fin n`; all expectations use the specified probability laws. -/
theorem lemma_5_3_1 {n d : ℕ} (hd : 3 ≤ d) (hnd : d < n)
    (c : Fin n → Point d) (b : Fin n → ℝ) (z : Point d)
    (hcenterLo : 1 / 2 < maxDataNorm c b)
    (hcenterHi : maxDataNorm c b ≤ 1)
    (σ : ℝ) (hσ : 0 < σ) :
    MeasureTheory.Integrable (fun p =>
      (secondPhaseSteps p.1.1 p.1.2 z p.2 : ℝ))
      ((gaussianInput c b σ).prod (sampleLaw n d)) ∧
    (∫ p, (secondPhaseSteps p.1.1 p.1.2 z p.2 : ℝ)
      ∂((gaussianInput c b σ).prod (sampleLaw n d))) ≤
      49 * Real.logb 2 ((n : ℝ) * d / min σ 1) *
      shadowBoundD n (d + 1) (min 1 (σ^5) /
        ((2 : ℝ)^23 * ((d + 1 : ℕ) : ℝ) ^ (11 / 2 : ℝ) *
          (n : ℝ)^14 * (Real.log n) ^ (5 / 2 : ℝ))) + n := by sorry

end SmoothedSimplex.TwoPhase
