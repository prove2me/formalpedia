-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_canonicalComponent_upper_self
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.canonicalComponent_upper_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:12:48.431435+00:00
-- url     : https://prove2.me/theorems/d279e976-bc25-4d1a-8083-377c286957d8
-- title:
--   BDL26 Original Piece Subsum Obstruction: canonical Component upper self
-- statement:
--   The BDL26 Original Piece Subsum Obstruction construction uses the canonical Component upper self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L238-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L238-L243

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.canonicalComponent_upper_self (S : OddScale) (j : Nat)
    (p : FamilyZ S (2*j+4) (TopIndex (2*j+4)))
    (hp : (upperSyndrome S j).val p ≠ 0) :
    p ∈ upperRegion S j (canonicalComponent S j p hp) := by sorry
