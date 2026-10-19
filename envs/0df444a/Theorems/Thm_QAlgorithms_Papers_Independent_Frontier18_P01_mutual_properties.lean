-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_mutual_properties
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.mutual_properties
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:42:45.376856+00:00
-- url     : https://prove2.me/theorems/1d24ffcf-c5f4-4b7b-a46d-745a8f523672
-- title:
--   Proposition 1: five properties of mutual information
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. The function $(\rho,\Phi)\mapsto I(\rho,\Phi)$ is nonnegative and jointly lower semicontinuous for trace-norm state topology and pointwise trace-norm channel topology. For $0\le t\le1$, states $\rho,\sigma$, and compatible channels, all five properties hold:
--
--   $$\begin{aligned}
--   I(t\rho+(1-t)\sigma,\Phi)&\ge tI(\rho,\Phi)+(1-t)I(\sigma,\Phi),\\
--   I(\rho,t\Phi+(1-t)\Psi)&\le tI(\rho,\Phi)+(1-t)I(\rho,\Psi),\\
--   I(\rho,\Psi\circ\Phi)&\le I(\rho,\Phi),\\
--   I(\rho,\Psi\circ\Phi)&\le I(\Phi(\rho),\Psi),\\
--   I(\omega,\Phi\otimes\Psi)&\le I(\omega_A,\Phi)+I(\omega_C,\Psi).
--   \end{aligned}$$
--
--   In the last line $\omega$ is any state on $A\otimes C$, with its indicated marginals, and $\Phi:A\to B$, $\Psi:C\to D$. Extended multiplication uses $0\cdot\infty=0$. These statements extend the usual information inequalities to infinite dimensions.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 7, Proposition 1: five properties of mutual information

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Proposition 1, PDF pp.7–10: joint lower semicontinuity and all five clauses.
Nonnegativity is built into the extended nonnegative codomain. -/
theorem mutual_properties [Countable I] [Countable J] [Countable K] [Countable L] :
    LowerSemicontinuous (fun p : State I × Channel I J => mutualInformation p.1.coefficients p.2.val) ∧
    (∀ (Phi : Channel I J) (rho sigma : State I) (t : ℝ), t ∈ Set.Icc 0 1 →
      ENNReal.ofReal t * mutualInformation rho.coefficients Phi.val +
        ENNReal.ofReal (1-t) * mutualInformation sigma.coefficients Phi.val ≤
          mutualInformation (convexOperatorMixture t rho.coefficients sigma.coefficients) Phi.val) ∧
    (∀ (rho : State I) (Phi Psi : Channel I J) (t : ℝ), t ∈ Set.Icc 0 1 →
      mutualInformation rho.coefficients (fun X => convexOperatorMixture t (Phi.val X) (Psi.val X)) ≤
        ENNReal.ofReal t * mutualInformation rho.coefficients Phi.val +
          ENNReal.ofReal (1-t) * mutualInformation rho.coefficients Psi.val) ∧
    (∀ (rho : State I) (Phi : Channel I J) (Psi : Channel J K),
      mutualInformation rho.coefficients (Psi.val ∘ Phi.val) ≤ mutualInformation rho.coefficients Phi.val) ∧
    (∀ (rho : State I) (Phi : Channel I J) (Psi : Channel J K),
      mutualInformation rho.coefficients (Psi.val ∘ Phi.val) ≤ mutualInformation (Phi.val rho.coefficients) Psi.val) ∧
    (∀ (omega : State (I × K)) (Phi : Channel I J) (Psi : Channel K L),
      mutualInformation omega.coefficients (channelTensorAction Phi.val Psi.val) ≤
        mutualInformation (traceSecond omega.coefficients) Phi.val +
          mutualInformation (traceFirst omega.coefficients) Psi.val) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
