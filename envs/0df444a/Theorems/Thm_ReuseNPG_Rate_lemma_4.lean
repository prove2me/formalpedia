-- Prove2me | Theorems.Thm_ReuseNPG_Rate_lemma_4
-- name    : ReuseNPG.Rate.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:07.918411+00:00
-- url     : https://prove2.me/theorems/68c6bfbe-38c3-4849-a202-adf667510021
-- title:
--   Lemma 4, p. 12 — covariance of the fresh-gradient noise
-- statement:
--   Let a finite discounted MDP, a differentiable policy family, and an RNPG run with batch size $B\ge1$, gradient reuse size $K\ge1$, positive Fisher regularization, and a compact convex parameter set satisfy Assumptions 1 and 2. The run uses independent fresh gradient and Fisher batches. Suppose its iterates converge almost surely to $\bar\theta$ in the interior of the parameter set, and let $\mathcal G$ be the Hurwitz linearization matrix.
--
--   Let $L_i$ be the mean inverse-Fisher matrix times the fresh batch's centered policy-gradient sum, scaled by $1/(KB)$. As starting time $n$ and window length $m$ tend to infinity simultaneously, almost surely,
--
--   $$
--   \frac1m\sum_{i=n}^{n+m-1}
--   \mathbb E[L_iL_i^T-\Sigma_1(\bar\theta)/(K^2B)\mid\mathcal F_n]\longrightarrow0.
--   $$
--
--   This identifies the covariance contribution from the fresh gradient batch, before accounting for memory reuse and random inverse-Fisher estimation.
--
--   **Formalization Note** State and action spaces are finite and nonempty, the parameter dimension is positive, and $\bar\theta\in\operatorname{interior}\Theta$ is added to exclude a false boundary Gaussian claim. A separate Fisher batch realizes Assumption 1(A.1.7); early iterations average the batches available. Conditional expectations of matrices are taken entrywise given the run's past filtration $\mathcal F_n$.
-- source:
--   Lin, Wang & Zhou, Reusing historical trajectories in natural policy gradient via importance sampling, arXiv:2403.00675v2, p. 12, Lemma 4; Appendix A.7, p. 22

import Mathlib
import Definitions.Def_ReuseNPG_Rate_Model

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace ReuseNPG.Rate

/-- Lemma 4, p. 12: averaged conditional covariance of Lₙ. -/
theorem lemma_4 {S A : Type*} [Fintype S] [Fintype A]
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
      (fun i ω => outer (Lnoise (B := B) (K := K) M π ε θ ξ i ω)
        (Lnoise (B := B) (K := K) M π ε θ ξ i ω))
      (((K : ℝ)^2 * B)⁻¹ • Sigma1 (B := B) M π ε θbar) := by sorry

end ReuseNPG.Rate
