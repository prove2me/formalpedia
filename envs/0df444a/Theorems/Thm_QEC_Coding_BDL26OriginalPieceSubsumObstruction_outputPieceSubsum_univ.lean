-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_outputPieceSubsum_univ
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.outputPieceSubsum_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:01:34.167913+00:00
-- url     : https://prove2.me/theorems/397fe2eb-7c67-4d2d-b1c5-4b0d6c706482
-- title:
--   BDL26 Original Piece Subsum Obstruction: output Piece Subsum univ
-- statement:
--   Summing every original position recovers the actual original correction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L36-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L36-L41

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.outputPieceSubsum_univ (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (O : AssemblyStepOutput (indexedDecoderData S depth) i) :
    outputPieceSubsum S depth i O Finset.univ = O.correction := by sorry
