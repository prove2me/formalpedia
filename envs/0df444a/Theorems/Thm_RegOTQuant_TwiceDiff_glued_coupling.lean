-- Prove2me | Theorems.Thm_RegOTQuant_TwiceDiff_glued_coupling
-- name    : RegOTQuant.TwiceDiff.glued_coupling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:01.38171+00:00
-- url     : https://prove2.me/theorems/f88c1408-b3ce-4ad5-87b6-2dc6460b3855
-- title:
--   Theorem 3.8 proof, pp. 15–16 — restored marginals and data processing
-- statement:
--   Let $\widetilde\pi\in\mathcal P^n(X)$ be a finite approximation of a joint law. For each coordinate $i$, suppose $\theta_i$ is a finite-cost martingale coupling from the $i$th marginal of $\widetilde\pi$ to the prescribed marginal $\mu_i$. Under the setting and corrected Hessian bound of Theorem 3.8, there is a coupling $\pi\in\Pi(\mu_1,\ldots,\mu_N)$ with
--
--   $$
--   \left|\int c\,d\pi-\int c\,d\widetilde\pi\right|\le B\sum_i\int\|x_i-y_i\|^2\,d\theta_i,
--   \qquad D_f(\pi,P)\le D_f\left(\widetilde\pi,\bigotimes_i\mu_i^n\right).
--   $$
--
--   Here $\mu_i^n$ is the $i$th marginal of $\widetilde\pi$. The statement records the cost and divergence properties of the coupling constructed by combining the coordinate kernels in the paper.
-- source:
--   Eckstein & Nutz, Convergence rates for regularized optimal transport via quantization, arXiv:2208.14391v3, pp. 15–16, proof of Theorem 3.8, displays before (3.7) and after (3.7)

import Mathlib
import Definitions.Def_RegOTQuant_TwiceDiff_Setting

open MeasureTheory Set

namespace RegOTQuant.TwiceDiff

/-- The glued coupling construction in the proof of Theorem 3.8, pp. 15–16.
The existential witness is the second marginal of the kernel product described there. -/
theorem glued_coupling {N : ℕ} {d : Fin N → ℕ}
    (Xs : ∀ i : Fin N, Set (Fi d i)) (μ : ∀ i : Fin N, Measure (Fi d i))
    (c : E d → ℝ) (B : ℝ) (f : ℝ → ℝ)
    (hset : Setting Xs μ c) (hB : 0 ≤ B) (hH : HessBound Xs c B)
    (hf : FStanding f)
    (n : ℕ) (πt : Measure (E d)) (θ : ∀ i : Fin N, Measure (Fi d i × Fi d i))
    (hπt : IsAtMostN n (X Xs) πt)
    (hθ : ∀ i, IsProbabilityMeasure (θ i) ∧
      (θ i).map Prod.fst = marginal πt i ∧
      (θ i).map Prod.snd = μ i ∧
      IsMartingaleCpl (θ i) ∧
      (∫⁻ z : Fi d i × Fi d i,
        ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂(θ i)) < ⊤) :
    ∃ π : Measure (E d), π ∈ couplings μ ∧
      |(∫ x, c x ∂π) - (∫ x, c x ∂πt)| ≤
        B * (∑ i, ∫ z : Fi d i × Fi d i, ‖z.1 - z.2‖ ^ 2 ∂(θ i)) ∧
      fDiv f π (prodRef μ) ≤ fDiv f πt (prodRef (marginal πt)) := by sorry

end RegOTQuant.TwiceDiff
