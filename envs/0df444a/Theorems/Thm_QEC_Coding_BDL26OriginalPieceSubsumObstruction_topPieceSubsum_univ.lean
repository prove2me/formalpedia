-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_topPieceSubsum_univ
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.topPieceSubsum_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:09:15.037856+00:00
-- url     : https://prove2.me/theorems/b6ccaf05-1ded-4890-a966-8f1834de079a
-- title:
--   BDL26 Original Piece Subsum Obstruction: top Piece Subsum univ
-- statement:
--   The BDL26 Original Piece Subsum Obstruction construction uses the top Piece Subsum univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L89-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L89-L91

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.topPieceSubsum_univ (S : OddScale) (j : Nat) :
    topPieceSubsum S j Finset.univ = (topOutput S j).correction := by sorry
