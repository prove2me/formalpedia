-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_topPieceSubsum_singleton
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.topPieceSubsum_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:08:42.755462+00:00
-- url     : https://prove2.me/theorems/9e38980a-2aa1-4fa1-9acb-a66bedeebb1f
-- title:
--   BDL26 Original Piece Subsum Obstruction: top Piece Subsum singleton
-- statement:
--   The BDL26 Original Piece Subsum Obstruction construction uses the top Piece Subsum singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L84-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L84-L87

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.topPieceSubsum_singleton (S : OddScale) (j : Nat)
    (a : Fin (topOutput S j).localComponents.length) :
    topPieceSubsum S j {a} = (topOutput S j).componentAt a := by sorry
