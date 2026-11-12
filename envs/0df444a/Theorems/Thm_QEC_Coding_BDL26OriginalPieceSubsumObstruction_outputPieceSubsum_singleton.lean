-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_outputPieceSubsum_singleton
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.outputPieceSubsum_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:02:13.492305+00:00
-- url     : https://prove2.me/theorems/d5cf6537-5c53-4160-a0cf-575f40bf418c
-- title:
--   BDL26 Original Piece Subsum Obstruction: output Piece Subsum singleton
-- statement:
--   The BDL26 Original Piece Subsum Obstruction construction uses the output Piece Subsum singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L30-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L30-L33

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.outputPieceSubsum_singleton (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (O : AssemblyStepOutput (indexedDecoderData S depth) i)
    (a : Fin O.localComponents.length) :
    outputPieceSubsum S depth i O {a} = O.componentAt a := by sorry
