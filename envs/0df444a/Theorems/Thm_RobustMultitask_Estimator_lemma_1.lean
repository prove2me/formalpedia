-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_lemma_1
-- name    : RobustMultitask.Estimator.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:41.944764+00:00
-- url     : https://prove2.me/theorems/ded41b4e-d5ca-4db6-af1d-2e6391b7046f
-- title:
--   Lemma 1, p. 41 — P[(2/nⱼ)‖Xʲᵀεʲ‖_∞ ≤ λⱼ/2] ≥ 1 − 2d exp(−λⱼ²nⱼ/(32σⱼ²))
-- statement:
--   Work in the fixed-design multitask model (design matrices standardized as in (1), independent mean-zero $\sigma_j$-subgaussian noise). For a task $j$ and a regularization level $\lambda_j>0$, define the event
--   $$\mathcal H^j=\Big\{\frac{2}{n_j}\big\|X^{j\top}\epsilon^j\big\|_\infty\le\frac{\lambda_j}{2}\Big\}.\qquad(15)$$
--   Then
--   $$\mathbb P\big[\mathcal H^j\big]\ \ge\ 1-2d\exp\Big(-\frac{\lambda_j^2n_j}{32\sigma_j^2}\Big).$$
--
--   On $\mathcal H^j$ the noise is dominated by the LASSO penalty, which is what makes the deterministic LASSO analysis in the proof of Proposition 5 apply.
--
--   **Formalization Note** The conclusion is stated as $\mathbb P[(\mathcal H^j)^c]\le 2d\exp(-\lambda_j^2n_j/(32\sigma_j^2))$, using the outer measure of the complement, which equals the printed form for the measurable event $\mathcal H^j$. The regularization level is positive, $\lambda_j>0$, as everywhere in the paper ($\lambda_j=\lambda/\sqrt{n_j}$); for $\lambda_j<0$ the event $\mathcal H^j$ is empty and the bound would fail.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 41, Lemma 1 and eq. (15)

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_Model

namespace RobustMultitask.Estimator

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

/-- Lemma 1, p. 41. In the fixed-design multitask model, for task `j` and any `λ_j > 0`, the event
`ℋʲ = {(2/n_j) ‖Xʲᵀ εʲ‖_∞ ≤ λ_j/2}` of (15) fails with probability at most
`2d exp(−λ_j² n_j / (32 σ_j²))`, i.e. `P[ℋʲ] ≥ 1 − 2d exp(−λ_j² n_j / (32 σ_j²))`. -/
theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} (n : Fin N → ℕ) (X : (j : Fin N) → Matrix (Fin (n j)) (Fin d) ℝ)
    (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ) (σ : Fin N → ℝ≥0)
    (ε : (j : Fin N) → Fin (n j) → Ω → ℝ)
    (hmodel : IsMultitaskModel P n X β βdag s σ ε) (j : Fin N) (lam : ℝ) (hlam : 0 < lam) :
    P {ω | ¬ ((2 / (n j : ℝ)) * linf ((X j)ᵀ *ᵥ (fun k => ε j k ω)) ≤ lam / 2)}
      ≤ ENNReal.ofReal
          (2 * d * Real.exp (-(lam ^ 2 * (n j : ℝ)) / (32 * (σ j : ℝ) ^ 2))) := by sorry

end RobustMultitask.Estimator
