-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_energy_constrained_continuity
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.energy_constrained_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:52:45.92286+00:00
-- url     : https://prove2.me/theorems/3104b7a3-2553-4520-99d9-3f473eeb679d
-- title:
--   Example 1: energy-constrained continuity and attained bounds
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $H$ be a semibounded self-adjoint Hamiltonian satisfying $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$, and let $h>0$ be finite. Set $K_{H,h}=\{\rho:\operatorname{Tr}(H\rho)\le h\}$. Entropy is finite and continuous on this ball, and for every channel $\Phi$,
--
--   $$\rho\mapsto I(\rho,\Phi),\qquad \rho\mapsto I_c(\rho,\Phi)$$
--
--   are continuous and bounded there. Each function attains its maximum whenever $K_{H,h}$ is nonempty. This yields energy-constrained optimization without receiver-entropy restrictions. The nonemptiness condition corrects the printed attainment assertion: $H=2\mathbf1$ and $h=1$ give an empty ball even in one dimension.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 20, Example 1: energy-constrained continuity and attained bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Example 1, PDF p.20. Printed: unconditional attainment on K_{H,h}.
Changed: attainment requires this ball to be nonempty. Reason: H=2 Id and h=1
have empty ball despite the Gibbs condition. Continuity and boundedness hold
also for the empty ball; no receiver-entropy condition is imposed. -/
theorem energy_constrained_continuity [Countable I] [Countable J] (H : Hamiltonian I) (hgibbs : H.gibbs)
    (Phi : Channel I J) (h : ℝ) (hh : 0 < h) :
    (∀ rho ∈ H.ball h, homogeneousEntropy rho.coefficients < ⊤) ∧
    ContinuousOn (fun rho : State I => (homogeneousEntropy rho.coefficients).toReal) (H.ball h) ∧
    ContinuousOn (fun rho : State I => mutualInformation rho.coefficients Phi.val) (H.ball h) ∧
    ContinuousOn (fun rho : State I => finiteInputCoherentInfo rho.coefficients Phi.val) (H.ball h) ∧
    (∃ M : ℝ, ∀ rho ∈ H.ball h, mutualInformation rho.coefficients Phi.val ≤ ENNReal.ofReal M ∧
      |finiteInputCoherentInfo rho.coefficients Phi.val| ≤ M) ∧
    ((H.ball h).Nonempty →
      (∃ rho ∈ H.ball h, ∀ sigma ∈ H.ball h,
        mutualInformation sigma.coefficients Phi.val ≤ mutualInformation rho.coefficients Phi.val) ∧
      (∃ rho ∈ H.ball h, ∀ sigma ∈ H.ball h,
        finiteInputCoherentInfo sigma.coefficients Phi.val ≤ finiteInputCoherentInfo rho.coefficients Phi.val)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
