-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_outputPieceSubsum_empty
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.outputPieceSubsum_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:01:49.856194+00:00
-- url     : https://prove2.me/theorems/1e60b409-1675-432b-9f69-8e90a8487bd1
-- title:
--   BDL26 Original Piece Subsum Obstruction: output Piece Subsum empty
-- statement:
--   The BDL26 Original Piece Subsum Obstruction construction uses the output Piece Subsum empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L26-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L26-L28

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.outputPieceSubsum_empty (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (O : AssemblyStepOutput (indexedDecoderData S depth) i) :
    outputPieceSubsum S depth i O ∅ = 0 := by sorry
