-- Prove2me | Theorems.Thm_ReuseNPG_Rate_lemma_8
-- name    : ReuseNPG.Rate.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:34.772476+00:00
-- url     : https://prove2.me/theorems/61614989-67db-4795-ba4f-81338d836e6e
-- title:
--   Lemma 8, p. 13, (12) — fixed-state memory cross covariance
-- statement:
--   Let a finite discounted MDP, a differentiable policy family, and an RNPG run with batch size $B\ge1$, gradient reuse size $K\ge1$, positive Fisher regularization, and a compact convex parameter set satisfy Assumptions 1 and 2. The run uses independent fresh gradient and Fisher batches. Suppose its iterates converge almost surely to $\bar\theta$ in the interior of the parameter set, and let $\mathcal G$ be the Hurwitz linearization matrix.
--
--   Let $\Gamma_i(\bar\theta,e_i)$ be the source's weighted infinite series of future conditional-mean deviations, and let $\Lambda_i(\bar\theta,e_i)$ be its conditional cross moment with the preconditioned gradient estimate. As $n,m\to\infty$ simultaneously, almost surely,
--
--   $$
--   \frac1m\sum_{i=n}^{n+m-1}
--   \mathbb E\!\left[
--   \Lambda_i(\bar\theta,e_i)
--   -\frac{K-1}{2KB}\Sigma_1(\bar\theta)
--   \middle|e_n(\bar\theta)\right]\longrightarrow0.
--   $$
--
--   This supplies the cross contribution of stored-history mean and martingale noise in the covariance of Theorem 2.
--
--   **Formalization Note** State and action spaces are finite and nonempty, the parameter dimension is positive, and $\bar\theta\in\operatorname{interior}\Theta$ is added to exclude a false boundary Gaussian claim. A separate Fisher batch realizes Assumption 1(A.1.7); early iterations average the batches available. The series defining $\Gamma_i$ is a true infinite sum; the fixed-state expectation is the finite memory-chain operator.
-- source:
--   Lin, Wang & Zhou, Reusing historical trajectories in natural policy gradient via importance sampling, arXiv:2403.00675v2, p. 13, Lemma 8 and equation (12); Appendix A.11, pp. 24–25

import Mathlib
import Definitions.Def_ReuseNPG_Rate_FixedState

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace ReuseNPG.Rate

/-- Lemma 8, p. 13, equation (12): fixed-state cross covariance. -/
theorem lemma_8 {S A : Type*} [Fintype S] [Fintype A]
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
    FsCesaroLimit M π θbar P
      (memRun (B := B) (K := K) M π θ ξ)
      (fun i e => Lambda (B := B) (K := K) M π α ε θbar i e)
      ((((K - 1 : ℕ) : ℝ) / (2 * (K : ℝ) * B)) • Sigma1 (B := B) M π ε θbar) := by sorry

end ReuseNPG.Rate
