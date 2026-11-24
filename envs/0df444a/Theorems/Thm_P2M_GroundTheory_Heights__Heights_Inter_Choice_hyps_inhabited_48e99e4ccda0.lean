-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_Choice_hyps_inhabited_48e99e4ccda0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_Choice_hyps_inhabited_48e99e4ccda0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:38.454978+00:00
-- url     : https://prove2.me/theorems/57549ba9-4543-4acb-b58d-e0292100c5ec
-- title:
--   P2 M Ground Theory Heights  Heights Inter Choice hyps inhabited 48e99e4ccda0: P2 M Ground Theory Heights  Heights Inter Choice hyps inhabited 48e99e4ccda0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Choice hyps inhabited 48e99e4ccda0 construction uses the P2 M Ground Theory Heights  Heights Inter Choice hyps inhabited 48e99e4ccda0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L229-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean#L229-L235

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

theorem P2M_GroundTheory_Heights__Heights_Inter_Choice_hyps_inhabited_48e99e4ccda0 :
    IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 ∧
      ∀ i : Fin 1, IsMultiProjPrime ((fun _ => ⊥ : Fin 1 → Ideal (MRing (PBlk 2))) i) ∧
        ⊥ ≤ (fun _ => ⊥ : Fin 1 → Ideal (MRing (PBlk 2))) i ∧
        (fun _ => ⊥ : Fin 1 → Ideal (MRing (PBlk 2))) i ≤ (fun _ => ptTwo) i ∧
        IsClosedPt ((fun _ => ptTwo : Fin 1 → Ideal (MRing (PBlk 2))) i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«Choice».«hyps_inhabited» := P2M_GroundTheory_Heights__Heights_Inter_Choice_hyps_inhabited_48e99e4ccda0
