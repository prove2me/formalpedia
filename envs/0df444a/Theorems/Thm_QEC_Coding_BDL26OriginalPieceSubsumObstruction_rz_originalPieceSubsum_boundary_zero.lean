-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_rz_originalPieceSubsum_boundary_zero
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.rz_originalPieceSubsum_boundary_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:07:11.970193+00:00
-- url     : https://prove2.me/theorems/7489c1ec-c4ca-4df9-bca0-99d08ce34a79
-- title:
--   BDL26 Original Piece Subsum Obstruction: rz original Piece Subsum boundary zero
-- statement:
--   Actual embedded valid RZ inputs, with no supplied zero-boundary certificate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L44-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L44-L61

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.rz_originalPieceSubsum_boundary_zero (S : OddScale) (depth : Nat)
    (i : StepIndex depth) (h : ¬i.val % 2 = 0)
    (s : (indexedFamily S depth).Syndrome i.castSucc)
    (A : Finset (Fin (BDL26RZDecoderAdapter.rzStepOutput S depth i h
      (BDL26RZDecoderAdapter.embeddedSyndrome S depth i s)).localComponents.length)) :
    (indexedFamily S depth).coboundary1 i.succ
      (outputPieceSubsum S depth i
        (BDL26RZDecoderAdapter.rzStepOutput S depth i h
          (BDL26RZDecoderAdapter.embeddedSyndrome S depth i s)) A) = 0 := by sorry
