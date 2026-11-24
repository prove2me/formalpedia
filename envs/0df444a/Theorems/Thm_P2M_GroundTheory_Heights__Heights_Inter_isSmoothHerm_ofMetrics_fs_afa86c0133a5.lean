-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_ofMetrics_fs_afa86c0133a5
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_ofMetrics_fs_afa86c0133a5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:46.554158+00:00
-- url     : https://prove2.me/theorems/98f9484b-1aa4-4d77-9562-ffb3d3df2af3
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Smooth Herm of Metrics fs afa86c0133a5: P2 M Ground Theory Heights  Heights Inter is Smooth Herm of Metrics fs afa86c0133a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Smooth Herm of Metrics fs afa86c0133a5 construction uses the P2 M Ground Theory Heights  Heights Inter is Smooth Herm of Metrics fs afa86c0133a5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L581-L601
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsAntisym.lean#L581-L601

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_TsgPolyVolPolyCoeffEven
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsAntisym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ComplexOrder ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
attribute [instance] ProjectiveLineBundle.fieldΩ ProjectiveLineBundle.finι ProjectiveLineBundle.finν ProjectiveLineBundle.finκ ProjectiveLineBundle.acgE ProjectiveLineBundle.modE
  ProjectiveLineBundle.fieldΦ ProjectiveLineBundle.algΦ
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_ofMetrics_fs_afa86c0133a5 (a : K → ℤ) : IsSmoothHerm (HermLine.ofMetrics (fun k => fsMetric (ι k)) a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isSmoothHerm_ofMetrics_fs» := P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_ofMetrics_fs_afa86c0133a5
