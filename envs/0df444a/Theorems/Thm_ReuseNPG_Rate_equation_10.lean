-- Prove2me | Theorems.Thm_ReuseNPG_Rate_equation_10
-- name    : ReuseNPG.Rate.equation_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:23.351501+00:00
-- url     : https://prove2.me/theorems/b6262058-059e-4bcd-907d-7094366a3ff5
-- title:
--   (10), p. 12 — combined martingale-noise covariance
-- statement:
--   Let a finite discounted MDP, a differentiable policy family, and an RNPG run with batch size $B\ge1$, gradient reuse size $K\ge1$, positive Fisher regularization, and a compact convex parameter set satisfy Assumptions 1 and 2. The run uses independent fresh gradient and Fisher batches. Suppose its iterates converge almost surely to $\bar\theta$ in the interior of the parameter set, and let $\mathcal G$ be the Hurwitz linearization matrix.
--
--   Write $\delta G_i=L_i+R_i$ for the martingale fluctuation in the source's decomposition. As $n,m\to\infty$ simultaneously, almost surely,
--
--   $$
--   \frac1m\sum_{i=n}^{n+m-1}
--   \mathbb E\!\left[\delta G_i\delta G_i^T
--   -\frac{\Sigma_1(\bar\theta)}{K^2B}
--   -\frac{\Sigma_2(\bar\theta)}{KB}
--   \middle|\mathcal F_n\right]\longrightarrow0.
--   $$
--
--   This combines the three preceding conditional covariance statements and is the martingale-noise part of Theorem 2.
--
--   **Formalization Note** State and action spaces are finite and nonempty, the parameter dimension is positive, and $\bar\theta\in\operatorname{interior}\Theta$ is added to exclude a false boundary Gaussian claim. A separate Fisher batch realizes Assumption 1(A.1.7); early iterations average the batches available. Conditional expectations are entrywise given $\mathcal F_n$.
-- source:
--   Lin, Wang & Zhou, Reusing historical trajectories in natural policy gradient via importance sampling, arXiv:2403.00675v2, p. 12, display (10), “With Lemma 4-6, we have”

import Mathlib
import Definitions.Def_ReuseNPG_Rate_Model

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace ReuseNPG.Rate

/-- (10), p. 12: averaged conditional covariance of δGₙ. -/
theorem equation_10 {S A : Type*} [Fintype S] [Fintype A]
    [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSingletonClass S] [MeasurableSingletonClass A]
    [Nonempty S] [Nonempty A] {d B K : ℕ} (hd : 0 < d) (hB : 1 ≤ B) (hK : 1 ≤ K)
    (M : MDP S A) (hM : M.Standing) (π : E d → S → A → ℝ)
    (hπ : IsPolicyFamily π) (Θ : Set (E d)) (α : ℕ → ℝ)
    (ε : ℝ) (hε : 0 < ε) (θ0 : E d) (hθ0 : θ0 ∈ Θ)
    {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (θ : ℕ → Ω → E d) (ξ ζ : ℕ → Ω → Fin B → S × A)
    (hrun : IsRNPGRun (K := K) M π Θ α ε θ0 P ℱ θ ξ ζ)
    (hA1 : Assumption1 M π Θ α) (θbar : E d) (Gm : DMat d)
    (hA2 : Assumption2 (B := B) M π Θ α ε P θ θbar Gm)
    (hθbar_int : θbar ∈ interior Θ) :
    CesaroCondLimit P ℱ
      (fun i ω => outer (deltaG (B := B) (K := K) M π ε θ ξ ζ i ω)
        (deltaG (B := B) (K := K) M π ε θ ξ ζ i ω))
      (((K : ℝ)^2 * B)⁻¹ • Sigma1 (B := B) M π ε θbar +
        (((K : ℝ) * B)⁻¹ • Sigma2 (B := B) M π ε θbar)) := by sorry

end ReuseNPG.Rate
