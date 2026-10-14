-- Prove2me | Theorems.Thm_QuantileSPQO_Rate_lemma_5
-- name    : QuantileSPQO.Rate.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:57.607637+00:00
-- url     : https://prove2.me/theorems/5eb05044-dec0-4688-8c87-9cfc5dcffeb1
-- title:
--   Lemma 5 — under A1–A3, B1, B2, √E‖D_k − ∇q(θ_k)‖² = O(α_k/γ_k) + O(c_k²) + O(β_k^{1/2}/c_k)
-- statement:
--   Under the hypotheses of Lemma 4 and, in addition, B2, the gradient tracker of SPQO satisfies
--   $$
--   \sqrt{E\big[\|D_k-\nabla_\theta q(\theta_k)\|^2\big]}=O\Big(\frac{\alpha_k}{\gamma_k}\Big)+O\big(c_k^2\big)+O\Big(\frac{\beta_k^{1/2}}{c_k}\Big).
--   $$
--
--   The three terms are the error inherited from the quantile tracker (Lemma 4), the bias of the simultaneous-perturbation estimator (Lemma 2), and its noise.
--
--   **Formalization Note** The conclusion is stated as: there is $C\ge0$ with $E\|D_k-\nabla q(\theta_k)\|^2\le\big(C(\alpha_k/\gamma_k+c_k^2+\beta_k^{1/2}/c_k)\big)^2$ for all large $k$. $\nabla q(\theta_k)$ is read where $q$ is $C^2$ (every iterate lies in $\Theta$). The expectation is a Lebesgue integral in $[0,\infty]$. Run and assumptions as in the Setting file.
-- source:
--   Hu, Song and Fu, Quantile Optimization via Multiple Timescale Local Search for Black-box Functions, arXiv:2308.07607v1, p. 18, Lemma 5 (standing assumptions p. 17)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace QuantileSPQO.Rate

theorem lemma_5 {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hΘ : IsConstraintSet Θ) (hM : IsQuantileModel M Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA1 : A1 P M R) (hA2 : A2 P ℱ R) (hA3a : A3a β c)
    (hA3b : A3b γ) (hA3c : A3c α) (hA3d : A3d α β γ)
    (hB1 : B1 P M R)
    (hB2 : B2 M Θ)
    (hpoly : PolySteps α β γ c)
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 M.qf U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∫⁻ ω, ‖R.D k ω - gradient M.qf (R.θ k ω)‖ₑ ^ 2 ∂P
        ≤ ENNReal.ofReal ((C * (α k / γ k + c k ^ 2 + Real.sqrt (β k) / c k)) ^ 2) := by sorry

end QuantileSPQO.Rate
