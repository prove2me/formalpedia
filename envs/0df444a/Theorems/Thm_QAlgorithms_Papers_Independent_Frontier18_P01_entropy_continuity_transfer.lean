-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_entropy_continuity_transfer
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.entropy_continuity_transfer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:51:36.326258+00:00
-- url     : https://prove2.me/theorems/1eec1395-654c-4517-869b-cbc66b13085e
-- title:
--   Proposition 4: continuity inherited from input entropy
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $\Phi$ be any channel and $A$ any subset of the input state space. Assume entropy is finite on $A$ and continuous there as a real-valued function. Then
--
--   $$\rho\longmapsto I(\rho,\Phi),\qquad \rho\longmapsto I_c(\rho,\Phi)$$
--
--   are continuous on $A$ in trace-norm topology. No compactness or output-entropy assumption is imposed. This transfers input-entropy continuity to the two information quantities; the finite-valued interpretation is the one required by Definition 5 and the source proof.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 19, Proposition 4: continuity inherited from input entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Proposition 4, PDF pp.19–20. Finite-valued entropy continuity is the domain
reading required by Definition 5 and the proof's difference of real functions. -/
theorem entropy_continuity_transfer [Countable I] [Countable J] (Phi : Channel I J) (A : Set (State I))
    (hfinite : ∀ rho ∈ A, homogeneousEntropy rho.coefficients < ⊤)
    (hcont : ContinuousOn (fun rho : State I => (homogeneousEntropy rho.coefficients).toReal) A) :
    ContinuousOn (fun rho : State I => mutualInformation rho.coefficients Phi.val) A ∧
    ContinuousOn (fun rho : State I => finiteInputCoherentInfo rho.coefficients Phi.val) A := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
