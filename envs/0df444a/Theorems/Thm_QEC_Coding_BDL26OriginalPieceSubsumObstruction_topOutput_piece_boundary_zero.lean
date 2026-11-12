-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_topOutput_piece_boundary_zero
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.topOutput_piece_boundary_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:01:24.025598+00:00
-- url     : https://prove2.me/theorems/a9531961-effd-4d1a-82e2-6ee72e5da164
-- title:
--   BDL26 Original Piece Subsum Obstruction: top Output piece boundary zero
-- statement:
--   All positions in the genuine actual top output have zero recorded boundary.
--   The entire dependent statement is transported before introducing its index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L65-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L65-L73

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.topOutput_piece_boundary_zero (S : OddScale) (j : Nat) :
    ∀ a : Fin (topOutput S j).localComponents.length,
      (topOutput S j).componentCoboundaryAt a = 0 := by sorry
