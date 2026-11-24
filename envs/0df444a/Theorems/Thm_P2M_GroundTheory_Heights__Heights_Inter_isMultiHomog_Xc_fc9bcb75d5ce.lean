-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_Xc_fc9bcb75d5ce
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_Xc_fc9bcb75d5ce
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:37.534807+00:00
-- url     : https://prove2.me/theorems/4b2a5a30-7d8d-42f2-bb6c-5715c6e2de93
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Multi Homog Xc fc9bcb75d5ce: P2 M Ground Theory Heights  Heights Inter is Multi Homog Xc fc9bcb75d5ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Multi Homog Xc fc9bcb75d5ce construction uses the P2 M Ground Theory Heights  Heights Inter is Multi Homog Xc fc9bcb75d5ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L143-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L143-L155

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_Xc_fc9bcb75d5ce (n : ℕ) (i : Fin n) : IsMultiHomog (Xc n i) (fun _ => 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isMultiHomog_Xc» := P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_Xc_fc9bcb75d5ce
