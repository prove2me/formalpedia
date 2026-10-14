-- Prove2me | Theorems.Thm_QuantileSPQO_Rate_theorem_1
-- name    : QuantileSPQO.Rate.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:57.499816+00:00
-- url     : https://prove2.me/theorems/cf38f968-0fb8-4120-b9a9-32503fc02ece
-- title:
--   Theorem 1 (strictly convex clause) — under A1–A3, θ_k → θ* w.p.1 when q is strictly convex on Θ
-- statement:
--   Let $(\theta_k,q_k,D_k)$ be a run of Algorithm SPQO for a black box with quantile function $q$ on a constraint set $\Theta\subseteq\mathbb R^d$, $d\ge1$, and assume A1, A2 and A3. Suppose that $q$ is continuously differentiable on an open set containing $\Theta$, that $q$ is strictly convex on $\Theta$, and that $\theta^*\in\Theta$ minimizes $q$ over $\Theta$ (so $\theta^*$ is the unique optimal solution of $\min_{\theta\in\Theta}q(\theta)$). Then
--   $$
--   \theta_k\longrightarrow\theta^*\qquad\text{almost surely.}
--   $$
--
--   This is the almost-sure convergence of SPQO, the starting point of the rate analysis of Section 4.
--
--   **Formalization Note** Only the second sentence of the paper's Theorem 1 is formalized; the first sentence (convergence to a limit set of the projected ODE (25)) is not. Continuous differentiability of $q$ near $\Theta$ is implicit in the paper (the ODE (25) is driven by $\nabla_\theta q$) and is stated. Run and assumptions as in the Setting file.
-- source:
--   Hu, Song and Fu, Quantile Optimization via Multiple Timescale Local Search for Black-box Functions, arXiv:2308.07607v1, p. 15, Theorem 1 (second sentence)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_QuantileSPQO_Rate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace QuantileSPQO.Rate

theorem theorem_1 {Ω : Type*} [m0 : MeasurableSpace Ω] {d : ℕ} (hd : 0 < d)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : Model d) (Θ : Set (E d)) (Proj : E d → E d) (I : Set ℝ) (Pq : ℝ → ℝ)
    (α β γ c : ℕ → ℝ) (R : Run Ω d)
    (hΘ : IsConstraintSet Θ) (hM : IsQuantileModel M Θ)
    (hProj : SpectralProjGrad.Shared.IsProjOnto Θ Proj)
    (hrun : IsSPQORun P ℱ M Θ Proj I Pq α β γ c R)
    (hA1 : A1 P M R) (hA2 : A2 P ℱ R) (hA3a : A3a β c)
    (hA3b : A3b γ) (hA3c : A3c α) (hA3d : A3d α β γ)
    (hq1 : ∃ U : Set (E d), IsOpen U ∧ Θ ⊆ U ∧ ContDiffOn ℝ 1 M.qf U)
    (hconv : StrictConvexOn ℝ Θ M.qf) (θstar : E d) (hθstar : θstar ∈ Θ)
    (hmin : IsMinOn M.qf Θ θstar) :
    ∀ᵐ ω ∂P, Tendsto (fun k => R.θ k ω) atTop (𝓝 θstar) := by sorry

end QuantileSPQO.Rate
