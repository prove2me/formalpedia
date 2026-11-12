-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_topPieceSubsum_boundary_zero
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.topPieceSubsum_boundary_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:02:22.330193+00:00
-- url     : https://prove2.me/theorems/0f8b97cd-4d25-4eed-8b42-5143011aec8d
-- title:
--   BDL26 Original Piece Subsum Obstruction: top Piece Subsum boundary zero
-- statement:
--   The BDL26 Original Piece Subsum Obstruction construction uses the top Piece Subsum boundary zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L93-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L93-L102

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.topPieceSubsum_boundary_zero (S : OddScale) (j : Nat)
    (A : Finset (Fin (topOutput S j).localComponents.length)) :
    (indexedFamily S (2*j+4)).coboundary1 (TopIndex (2*j+4))
      (topPieceSubsum S j A) = 0 := by sorry
