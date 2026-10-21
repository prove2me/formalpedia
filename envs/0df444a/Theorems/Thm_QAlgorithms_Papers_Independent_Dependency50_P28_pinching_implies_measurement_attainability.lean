-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_pinching_implies_measurement_attainability
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.pinching_implies_measurement_attainability
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:13:19.800749+00:00
-- url     : https://prove2.me/theorems/83baf4f1-a0f1-4350-ac70-58b3f00ea59d
-- title:
--   Asymptotic pinching attainment implies measurement attainment
-- statement:
--   For any divergence family D on density-operator pairs in all finite dimensions, let AAP mean convergence of n⁻¹D after pinching ρ^{⊗n} by σ^{⊗n}, and let AAM mean existence of an asymptotically attaining sequence of finite measurements. Then
--
--   $$
--   \mathrm{AAP}(D)\Longrightarrow\mathrm{AAM}(D).
--   $$
--
--   This connects pinching regularization to measurement regularization without extra assumptions on the divergence family.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 21, The following implication is obvious:

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.21: Asymptotic pinching attainment implies measurement attainment. Measurements in the definition may output commuting matrices in the same space. A pair-dependent joint-eigenbasis dephasing matches both pinched outputs exactly, without an unassumed basis-invariance hypothesis. -/
theorem pinching_implies_measurement_attainability (d : Divergence) :
    AAP d → AAM d := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
