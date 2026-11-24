-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ProjSpace_chart__str_475cb27b7b18
-- name    : P2M_GlobalTheory_ProjSpace_chart__str_475cb27b7b18
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:47:31.79626+00:00
-- url     : https://prove2.me/theorems/bf0c086c-e275-4396-b1bf-43d8aeee1e35
-- title:
--   P2 M Global Theory Proj Space chart  str 475cb27b7b18: P2 M Global Theory Proj Space chart  str 475cb27b7b18
-- statement:
--   The P2 M Global Theory Proj Space chart  str 475cb27b7b18 construction uses the P2 M Global Theory Proj Space chart  str 475cb27b7b18 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TwistingSheafOneChartEqPreimageStandardChart.lean#L426-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TwistingSheafOneChartEqPreimageStandardChart.lean#L426-L432

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

theorem P2M_GlobalTheory_ProjSpace_chart__str_475cb27b7b18 (i : Fin (N + 1)) :
    chartι R N i ≫ PSpace.str R N = spMap (C : R →+* MvPolynomial {j // j ≠ i} R) := by sorry

alias «GlobalTheory».«ProjSpace».«chartι_str» := P2M_GlobalTheory_ProjSpace_chart__str_475cb27b7b18
