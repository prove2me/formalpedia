-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_R1_hyps_inhabited_bed2c6b07b11
-- name    : P2M_GroundTheory_Heights__Heights_Inter_R1_hyps_inhabited_bed2c6b07b11
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:12.48416+00:00
-- url     : https://prove2.me/theorems/c20ab6e4-cc0c-4065-b00d-5e9aed5eca1f
-- title:
--   P2 M Ground Theory Heights  Heights Inter R1 hyps inhabited bed2c6b07b11: P2 M Ground Theory Heights  Heights Inter R1 hyps inhabited bed2c6b07b11
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter R1 hyps inhabited bed2c6b07b11 construction uses the P2 M Ground Theory Heights  Heights Inter R1 hyps inhabited bed2c6b07b11 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L162-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L162-L165

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

theorem P2M_GroundTheory_Heights__Heights_Inter_R1_hyps_inhabited_bed2c6b07b11 :
    IsArithVar (⊥ : Ideal (MRing (PBlk 1))) 1 ∧ IsSmoothHerm (fsLine 1) ∧
      IsSectionOn ⊥ (fsLine 1) (Xc 1 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«R1».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_Inter_R1_hyps_inhabited_bed2c6b07b11
