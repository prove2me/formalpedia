-- Prove2me | Theorems.Thm_ReuseNPG_Rate_theorem_2
-- name    : ReuseNPG.Rate.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:31.704433+00:00
-- url     : https://prove2.me/theorems/6b5baaa5-6639-4468-a209-f66e8cf2cb8b
-- title:
--   Theorem 2, p. 11 — asymptotic normality of the RNPG error
-- statement:
--   Let a finite discounted MDP, a differentiable policy family, and an RNPG run with batch size $B\ge1$, gradient reuse size $K\ge1$, positive Fisher regularization, and a compact convex parameter set satisfy Assumptions 1 and 2. The run uses independent fresh gradient and Fisher batches. Suppose its iterates converge almost surely to $\bar\theta$ in the interior of the parameter set, and let $\mathcal G$ be the Hurwitz linearization matrix.
--
--   For $E_n=(\theta_n-\bar\theta)/\sqrt{\alpha_n}$, the marginal RNPG error converges in distribution:
--
--   $$
--   E_n\Rightarrow\mathcal N(0,\Sigma_\infty),\qquad
--   \operatorname{vec}(\Sigma_\infty)
--   =-(\mathcal G\oplus\mathcal G)^{-1}
--   \operatorname{vec}\!\left(\frac{\Sigma_1(\bar\theta)}B+
--   \frac{\Sigma_2(\bar\theta)}{KB}\right).
--   $$
--
--   The result quantifies how reusing historical gradient samples changes the asymptotic covariance; the contribution from the joint gradient and inverse-Fisher randomness has coefficient $1/(KB)$.
--
--   **Formalization Note** State and action spaces are finite and nonempty, the parameter dimension is positive, and $\bar\theta\in\operatorname{interior}\Theta$ is added to exclude a false boundary Gaussian claim. A separate Fisher batch realizes Assumption 1(A.1.7); early iterations average the batches available. The formal goal is the theorem's “As a result” marginal convergence clause. Its process-level weak convergence to a stationary SDE is outside this mission. The Gaussian covariance is computed from the model and is positive semidefinite under the assumptions, rather than supplied as a free parameter.
-- source:
--   Lin, Wang & Zhou, Reusing historical trajectories in natural policy gradient via importance sampling, arXiv:2403.00675v2, p. 11, Theorem 2, “As a result” clause; proof p. 13

import Mathlib
import Definitions.Def_ReuseNPG_Rate_Model

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace ReuseNPG.Rate

/-- Theorem 2, p. 11, marginal asymptotic normality of the RNPG error.
The process-level SDE convergence is outside this mission. The interior-limit
condition is added because the stated Gaussian limit is false at a boundary. -/
theorem theorem_2 {S A : Type*} [Fintype S] [Fintype A]
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
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) => (Real.sqrt (α n))⁻¹ • (θ n ω - θbar))
      atTop id (fun _ => P)
      (multivariateGaussian 0 (SigmaInf Gm (SigmaHat (B := B) (K := K) M π ε θbar))) := by sorry

end ReuseNPG.Rate
