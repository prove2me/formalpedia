-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_lemma_5_3_2
-- name    : SmoothedSimplex.TwoPhase.lemma_5_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:29:44.196077+00:00
-- url     : https://prove2.me/theorems/48b2fab8-4ac0-4667-bf9f-cf8942a78427
-- title:
--   Lemma 5.3.2 (LP⁺ Shadow, part 2) — corrected dimension
-- statement:
--   Let $n>d\ge3$, and perturb $(\widetilde y_i,\widetilde a_i)$ independently by isotropic Gaussians of standard deviation $\rho_1>0$. Fix $y'_i$ satisfying $y'_i>3\|(\widetilde y_i,\widetilde a_i)\|$ and $y'_i>60n(d+1)^{3/2}(\ln n)^{3/2}\rho_1$ for every $i$. Define $a_i^+=((y'_i-y_i)/2,a_i)$ and $y_i^+=(y'_i+y_i)/2$. Then
--   $$\mathbb E\left|\operatorname{Shadow}_{(0,z),z^+}(a_1^+/y_1^+,\ldots,a_n^+/y_n^+)\right|\le e\,\mathcal D\!\left(n,d+1,\frac{\rho_1\min_i y'_i}{3(\max_i y'_i)^2}\right)+1.$$
--   This handles the transformed, non-Gaussian LP⁺ vectors. **Formalization Note** The dimension $d+1$ corrects the printed $d$ to match those lifted vectors and the use of Corollary 4.3.3.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 5.3.2, printed p. 83, PDF p. 83

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Lemma 5.3.2 (LP⁺ Shadow, part 2), printed p. 83, PDF p. 83. Corrected D’s dimension to d+1, matching the lifted vectors; otherwise the printed use of Corollary 4.3.3 has a dimension mismatch. Formalization Note: `[n]` is `Fin n`; all expectations use the specified probability laws. -/
theorem lemma_5_3_2 {n d : ℕ} (hd : 3 ≤ d) (hnd : d < n)
    (c : Fin n → Point d) (b y' : Fin n → ℝ) (z : Point d)
    (ρ : ℝ) (hρ : 0 < ρ)
    (h57 : ∀ i, 3 * Real.sqrt ((b i)^2 + ‖c i‖^2) < y' i)
    (h58 : ∀ i, 60 * (n : ℝ) * ((d + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ) *
      (Real.log n) ^ (3 / 2 : ℝ) * ρ < y' i) :
    MeasureTheory.Integrable (fun p =>
      let lifted : Fin n → Point (d + 1) := fun i =>
        (liftedRhs p.2 y' i)⁻¹ • liftedVector p.1 p.2 y' i
      ((shadow lifted (fun _ => 1) (liftedOldObjective z)
        (liftedNewObjective d)).card : ℝ)) (gaussianInput c b ρ) ∧
    (∫ p,
      (let lifted : Fin n → Point (d + 1) := fun i =>
        (liftedRhs p.2 y' i)⁻¹ • liftedVector p.1 p.2 y' i
      ((shadow lifted (fun _ => 1) (liftedOldObjective z)
        (liftedNewObjective d)).card : ℝ)) ∂(gaussianInput c b ρ)) ≤
      Real.exp 1 * shadowBoundD n (d + 1)
        (ρ * sInf (Set.range y') /
          (3 * (sSup (Set.range y'))^2)) + 1 := by sorry

end SmoothedSimplex.TwoPhase
