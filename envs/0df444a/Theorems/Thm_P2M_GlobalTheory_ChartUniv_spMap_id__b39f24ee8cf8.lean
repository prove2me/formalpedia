-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ChartUniv_spMap_id__b39f24ee8cf8
-- name    : P2M_GlobalTheory_ChartUniv_spMap_id__b39f24ee8cf8
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:03:01.393738+00:00
-- url     : https://prove2.me/theorems/715bc159-336d-4e57-bb5c-baf90c661d50
-- title:
--   P2 M Global Theory Chart Univ sp Map id  b39f24ee8cf8: P2 M Global Theory Chart Univ sp Map id  b39f24ee8cf8
-- statement:
--   The P2 M Global Theory Chart Univ sp Map id  b39f24ee8cf8 construction uses the P2 M Global Theory Chart Univ sp Map id  b39f24ee8cf8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsUniversalChartOfFormalGroupChart.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/IsUniversalChartOfFormalGroupChart.lean#L38-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartUniv
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]

theorem P2M_GlobalTheory_ChartUniv_spMap_id__b39f24ee8cf8 (A : Type) [CommRing A] [Algebra R A] : spMap (R₀ := R) (AlgHom.id R A) = 𝟙 _ := by sorry

alias «GlobalTheory».«ChartUniv».«spMap_id'» := P2M_GlobalTheory_ChartUniv_spMap_id__b39f24ee8cf8
