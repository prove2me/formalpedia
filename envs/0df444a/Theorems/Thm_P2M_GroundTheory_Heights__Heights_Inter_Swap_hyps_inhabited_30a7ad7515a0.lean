-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Swap_hyps_inhabited_30a7ad7515a0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Swap_hyps_inhabited_30a7ad7515a0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:49.003617+00:00
-- url     : https://prove2.me/theorems/13d4b589-c762-4c91-99ff-3a2f35bdc713
-- title:
--   P2 M Ground Theory Heights  Heights Inter Swap hyps inhabited 30a7ad7515a0: P2 M Ground Theory Heights  Heights Inter Swap hyps inhabited 30a7ad7515a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Swap hyps inhabited 30a7ad7515a0 construction uses the P2 M Ground Theory Heights  Heights Inter Swap hyps inhabited 30a7ad7515a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L176-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L176-L180

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DegreeGeneric_hyps_inhabited_36d80aab7c4b

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Swap_hyps_inhabited_30a7ad7515a0 :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) (0 + 2) ∧ IsSmoothHerm (fsLine 2) ∧
      IsSectionOn ⊥ (fsLine 2) (Xc 2 0) ∧ IsSectionOn ⊥ (fsLine 2) (Xc 2 1) ∧
      ∀ W, W ∈ divSupp (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) → W ∉ divSupp ⊥ (Xc 2 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Swap».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_Inter_Swap_hyps_inhabited_30a7ad7515a0
