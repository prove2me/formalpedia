-- Prove2me | Theorems.Thm_QEC_Coding_BDL26CanonicalHistoryMarks_localZWitness_marked
-- name    : QEC.Coding.BDL26CanonicalHistoryMarks.localZWitness_marked
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:32:54.770208+00:00
-- url     : https://prove2.me/theorems/7d543178-7509-4220-8fa4-455d03c1293f
-- title:
--   BDL26 Canonical History Marks: local ZWitness marked
-- statement:
--   Nonvacuous actual witness: an unparented G2 local-Z is genuinely marked.
--   It is not asserted to belong to the root component.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L82-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/CanonicalHistoryMarks/Consistency.lean#L82-L105

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformRXTail_Input
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26CanonicalHistoryMarks
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26ReplacementSupport MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26CanonicalHistoryMarks.localZWitness_marked (S : OddScale) :
    ∃ (x : BaseX) (f : DoubleCylinderFace baseTannerSquarePresentation x S),
      physicalNode S 0 0 (localZ S x f) ∈ marks S 0 (localZWitnessInput S) ∧
        parent S 1 (localZ S x f) = none := by sorry
