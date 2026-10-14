-- Prove2me | Theorems.Thm_QuantileSPQO_Rate_lemma_4
-- name    : QuantileSPQO.Rate.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:58.810622+00:00
-- url     : https://prove2.me/theorems/aeb0e0f5-e40b-46af-a80e-6501fb0cea10
-- title:
--   Lemma 4 — under A1–A3 and B1, √E[(q_k − q(θ_k))²] = O(α_k/γ_k) + O(γ_k^{1/2})
-- statement:
--   Let $(\theta_k,q_k,D_k)$ be a run of Algorithm SPQO for a black box with quantile function $q$ on a constraint set $\Theta\subseteq\mathbb R^d$, $d\ge1$. Assume A1–A3 and B1, together with the standing assumptions of Section 4: the step sizes have the forms $\alpha_k=a/(k+1)^\alpha$, $\beta_k=b/(k+1)^\beta$, $\gamma_k=r/(k+1)^\gamma$, $c_k=c/(k+1)^\tau$, and $q$ is twice continuously differentiable on an open set containing $\Theta$. Then
--   $$
--   \sqrt{E\big[(q_k-q(\theta_k))^2\big]}=O\Big(\frac{\alpha_k}{\gamma_k}\Big)+O\big(\gamma_k^{1/2}\big).
--   $$
--
--   The $O(\alpha_k/\gamma_k)$ term is the price of tracking a moving quantile $q(\theta_k)$; the $O(\gamma_k^{1/2})$ term is the rate of the quantile recursion at a fixed $\theta$.
--
--   **Formalization Note** The conclusion is stated as: there is $C\ge0$ with $E[(q_k-q(\theta_k))^2]\le\big(C(\alpha_k/\gamma_k+\gamma_k^{1/2})\big)^2$ for all large $k$, which is equivalent to the paper's sum of one-sided $O$-terms. The expectation is a Lebesgue integral in $[0,\infty]$. Run and assumptions as in the Setting file (truncated quantile step, $k+1$ in the step sizes).
-- source:
--   Hu, Song and Fu, Quantile Optimization via Multiple Timescale Local Search for Black-box Functions, arXiv:2308.07607v1, p. 18, Lemma 4 (standing assumptions p. 17)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace QuantileSPQO.Rate

theorem lemma_4 {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hΘ : IsConstraintSet Θ) (hM : IsQuantileModel M Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA1 : A1 P M R) (hA2 : A2 P ℱ R) (hA3a : A3a β c)
    (hA3b : A3b γ) (hA3c : A3c α) (hA3d : A3d α β γ)
    (hB1 : B1 P M R)
    (hpoly : PolySteps α β γ c)
    (hq2 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 2 M.qf U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∫⁻ ω, ENNReal.ofReal ((R.q k ω - M.qf (R.θ k ω)) ^ 2) ∂P
        ≤ ENNReal.ofReal ((C * (α k / γ k + Real.sqrt (γ k))) ^ 2) := by sorry

end QuantileSPQO.Rate
