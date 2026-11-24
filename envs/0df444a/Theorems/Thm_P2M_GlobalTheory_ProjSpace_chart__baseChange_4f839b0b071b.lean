-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ProjSpace_chart__baseChange_4f839b0b071b
-- name    : P2M_GlobalTheory_ProjSpace_chart__baseChange_4f839b0b071b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:46:20.418783+00:00
-- url     : https://prove2.me/theorems/26f090b1-10ad-4ae6-84e2-d04a03fb5278
-- title:
--   P2 M Global Theory Proj Space chart  base Change 4f839b0b071b: P2 M Global Theory Proj Space chart  base Change 4f839b0b071b
-- statement:
--   The P2 M Global Theory Proj Space chart  base Change 4f839b0b071b construction uses the P2 M Global Theory Proj Space chart  base Change 4f839b0b071b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TwistingSheafOneChartEqPreimageStandardChart.lean#L502-L525
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TwistingSheafOneChartEqPreimageStandardChart.lean#L502-L525

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace
variable (R : Type) [CommRing R] (N : ℕ)
variable {R N}
variable (R N)
variable {R N}
variable (R N)
variable {R} {R' : Type} [CommRing R'] (φ : R →+* R')

theorem P2M_GlobalTheory_ProjSpace_chart__baseChange_4f839b0b071b (i : Fin (N + 1)) :
    chartι R' N i ≫ baseChange N φ =
      spMap (MvPolynomial.map φ : MvPolynomial {j // j ≠ i} R →+* _) ≫ chartι R N i := by sorry

alias «GlobalTheory».«ProjSpace».«chartι_baseChange» := P2M_GlobalTheory_ProjSpace_chart__baseChange_4f839b0b071b
