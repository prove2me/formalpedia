-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_divSupp_X_disjoint_74521f1af0e6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_divSupp_X_disjoint_74521f1af0e6
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:13.814889+00:00
-- url     : https://prove2.me/theorems/a2ddd992-5347-4243-881f-54c5578cf3d2
-- title:
--   P2 M Ground Theory Heights  Heights Inter div Supp X disjoint 74521f1af0e6: P2 M Ground Theory Heights  Heights Inter div Supp X disjoint 74521f1af0e6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter div Supp X disjoint 74521f1af0e6 construction uses the P2 M Ground Theory Heights  Heights Inter div Supp X disjoint 74521f1af0e6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L167-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L167-L174

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

theorem P2M_GroundTheory_Heights__Heights_Inter_divSupp_X_disjoint_74521f1af0e6 :
    ∀ W, W ∈ divSupp (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) → W ∉ divSupp ⊥ (Xc 2 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«divSupp_X_disjoint» := P2M_GroundTheory_Heights__Heights_Inter_divSupp_X_disjoint_74521f1af0e6
