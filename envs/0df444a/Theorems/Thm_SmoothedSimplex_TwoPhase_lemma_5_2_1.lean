-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_lemma_5_2_1
-- name    : SmoothedSimplex.TwoPhase.lemma_5_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:29:32.680336+00:00
-- url     : https://prove2.me/theorems/8431079f-402d-454f-ab88-13d775025ee7
-- title:
--   Lemma 5.2.1 (LP′) — corrected inequality
-- statement:
--   Let $n>d\ge3$, $\max_i\|(\bar y_i,\bar a_i)\|\in(1/2,1]$, and $\sigma>0$. Independently perturb every entry of $A$ and $y$ by centered Gaussian noise of standard deviation $\sigma$, and use the paper's random collection of $d$-sets and uniform $\alpha\in A_{1/d^2}$. The first-phase shadow count satisfies
--   $$\mathbb E S'_z\le326nd(\ln n)\log_2\!\frac{dn}{\min(1,\sigma)}\;\mathcal D\!\left(n,d,\frac{\min(1,\sigma^4)}{12960d^{8.5}n^{14}(\ln n)^{2.5}}\right).$$
--   This is the LP′ contribution to the main theorem. **Formalization Note** The source prints equality, while its proof on page 71 establishes this upper bound. Integrability is asserted in the conclusion.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 5.2.1, printed p. 68, PDF p. 68

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Lemma 5.2.1 (LP′), printed p. 68, PDF p. 68. Corrected from the printed equality to ≤, as the proof on p. 71 establishes an upper bound. Formalization Note: `[n]` is `Fin n`; all expectations use the specified probability laws. -/
theorem lemma_5_2_1 {n d : ℕ} (hd : 3 ≤ d) (hnd : d < n)
    (c : Fin n → Point d) (b : Fin n → ℝ) (z : Point d)
    (hcenterLo : 1 / 2 < maxDataNorm c b)
    (hcenterHi : maxDataNorm c b ≤ 1)
    (σ : ℝ) (hσ : 0 < σ) :
    MeasureTheory.Integrable (fun p =>
      (firstPhaseSteps p.1.1 p.1.2 z p.2.1 p.2.2 : ℝ))
      ((gaussianInput c b σ).prod (algorithmLaw n d)) ∧
    (∫ p, (firstPhaseSteps p.1.1 p.1.2 z p.2.1 p.2.2 : ℝ)
      ∂((gaussianInput c b σ).prod (algorithmLaw n d))) ≤
      326 * (n : ℝ) * d * Real.log n *
      Real.logb 2 ((d : ℝ) * n / min 1 σ) *
      shadowBoundD n d (min 1 (σ^4) /
        (12960 * (d : ℝ) ^ (8.5 : ℝ) * (n : ℝ)^14 *
          (Real.log n) ^ (2.5 : ℝ))) := by sorry

end SmoothedSimplex.TwoPhase
