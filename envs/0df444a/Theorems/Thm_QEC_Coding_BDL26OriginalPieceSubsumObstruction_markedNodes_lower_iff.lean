-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_markedNodes_lower_iff
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.markedNodes_lower_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:04:37.989751+00:00
-- url     : https://prove2.me/theorems/f58323e0-e5ff-4f29-8525-585bf35a07e8
-- title:
--   BDL26 Original Piece Subsum Obstruction: marked Nodes lower iff
-- statement:
--   The BDL26 Original Piece Subsum Obstruction construction uses the marked Nodes lower iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L160-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L160-L174

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.markedNodes_lower_iff (S : OddScale) (j : Nat)
    (lower : Finset (StrictLowerNode S j)) (v : StrictLowerNode S j) :
    includeLowerNode S j v ∈ markedNodes S j lower ↔ v ∈ lower := by sorry
