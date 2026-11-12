-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_canonical_markedNodes_eq
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.canonical_markedNodes_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:10:52.382804+00:00
-- url     : https://prove2.me/theorems/d7e6ed83-098e-48b5-b247-0f6ac8b95fcf
-- title:
--   BDL26 Original Piece Subsum Obstruction: canonical marked Nodes eq
-- statement:
--   Exact equality retains every physical mark and the real G1/G0 root closure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L177-L191
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L177-L191

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.canonical_markedNodes_eq (S : OddScale) (j : Nat) :
    markedNodes S j (canonicalLowerMarks S j) = canonicalMarks S j := by sorry
