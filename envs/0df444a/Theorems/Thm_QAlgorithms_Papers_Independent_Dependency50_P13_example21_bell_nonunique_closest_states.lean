-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P13_example21_bell_nonunique_closest_states
-- name    : QAlgorithms.Papers.Independent.Dependency50.P13.example21_bell_nonunique_closest_states
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:16:37.671747+00:00
-- url     : https://prove2.me/theorems/cee13df2-0cf8-4e19-b24e-8901255d6d23
-- title:
--   Example 21: nonunique closest separable states for a Bell state
-- statement:
--   On two qubits let |Phi>=(|00>+|11>)/sqrt(2) and Phi=|Phi><Phi|. Define
--
--   $$ \sigma_1=\tfrac12\Phi+\tfrac16(I-\Phi),\qquad \sigma_2=\tfrac12\Phi+\tfrac14(|01\rangle\langle01|+|10\rangle\langle10|). $$
--
--   Phi, sigma_1, and sigma_2 are density operators; sigma_1 and sigma_2 are separable and distinct. With natural logarithms,
--
--   $$ D(\Phi\|\sigma_1)=D(\Phi\|\sigma_2)=E_R(\Phi)=\ln2. $$
--
--   Here E_R is the infimum over all separable two-qubit states. Finite-dimensional separability is equivalently a finite convex combination of product density matrices. The second input named rho_AB in printed (75) is corrected to the Bell state Phi defined in the example.
--
--   Thus a nonfaithful input can have more than one closest separable state.
-- source:
--   Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme, arXiv:2105.08091v3, PDF p. 19, Example 21: nonunique closest separable states for a Bell state

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Example 21, arXiv:2105.08091v3, PDF p.19, (74),(75).
Two distinct separable states attain REE equal to ln 2. The printed rho_AB in the second
divergence of (75) is corrected to the defined Bell state. Independent moderation is required. -/
theorem example21_bell_nonunique_closest_states :
    QAlgorithms.IsDensityMatrix bellState ∧
    QAlgorithms.IsDensityMatrix bellSigmaOne ∧ QAlgorithms.IsDensityMatrix bellSigmaTwo ∧
    QAlgorithms.Entanglement.IsSeparableDensity bellSigmaOne ∧
    QAlgorithms.Entanglement.IsSeparableDensity bellSigmaTwo ∧
    bellSigmaOne ≠ bellSigmaTwo ∧
    twoQubitRelativeEntropy bellState bellSigmaOne = ENNReal.ofReal (Real.log 2) ∧
    twoQubitRelativeEntropy bellState bellSigmaTwo = ENNReal.ofReal (Real.log 2) ∧
    twoQubitEntanglement bellState = ENNReal.ofReal (Real.log 2) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P13

end
