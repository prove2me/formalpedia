-- Prove2me | Theorems.Thm_ReuseNPG_Rate_lemma_7
-- name    : ReuseNPG.Rate.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:31:43.003388+00:00
-- url     : https://prove2.me/theorems/135131d7-bb75-4c44-94a6-f0558c796dc9
-- title:
--   Lemma 7, p. 12, (11) — fixed-state conditional-mean covariance
-- statement:
--   Let a finite discounted MDP, a differentiable policy family, and an RNPG run with batch size $B\ge1$, gradient reuse size $K\ge1$, positive Fisher regularization, and a compact convex parameter set satisfy Assumptions 1 and 2. The run uses independent fresh gradient and Fisher batches. Suppose its iterates converge almost surely to $\bar\theta$ in the interior of the parameter set, and let $\mathcal G$ be the Hurwitz linearization matrix.
--
--   At fixed parameter $\bar\theta$, let $e_i(\bar\theta)$ be the chain of $K-1$ stored batches and let $g(\bar\theta,e_i)$ be the conditional mean of the preconditioned gradient estimator. Conditioning on the starting memory, as $n,m\to\infty$ simultaneously, almost surely,
--
--   $$
--   \frac1m\sum_{i=n}^{n+m-1}
--   \mathbb E\!\left[
--   g(\bar\theta,e_i)g(\bar\theta,e_i)^T
--   -\frac{K-1}{K^2B}\Sigma_1(\bar\theta)
--   \middle|e_n(\bar\theta)\right]\longrightarrow0.
--   $$
--
--   The factor $K-1$ counts the batches retained in effective memory.
--
--   **Formalization Note** State and action spaces are finite and nonempty, the parameter dimension is positive, and $\bar\theta\in\operatorname{interior}\Theta$ is added to exclude a false boundary Gaussian claim. A separate Fisher batch realizes Assumption 1(A.1.7); early iterations average the batches available. Fixed-state conditional expectation uses the explicit finite memory-chain operator, evaluated at the run's stored memory.
-- source:
--   Lin, Wang & Zhou, Reusing historical trajectories in natural policy gradient via importance sampling, arXiv:2403.00675v2, p. 12, Lemma 7 and equation (11); Appendix A.10, p. 24

import Mathlib
import Definitions.Def_ReuseNPG_Rate_FixedState

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace ReuseNPG.Rate

/-- Lemma 7, p. 12, equation (11): fixed-state conditional mean covariance. -/
theorem lemma_7 {S A : Type*} [Fintype S] [Fintype A]
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
      (fun _ e => outer (fixedG (B := B) M π ε θbar e)
        (fixedG (B := B) M π ε θbar e))
      ((((K - 1 : ℕ) : ℝ) / ((K : ℝ)^2 * B)) • Sigma1 (B := B) M π ε θbar) := by sorry

end ReuseNPG.Rate
