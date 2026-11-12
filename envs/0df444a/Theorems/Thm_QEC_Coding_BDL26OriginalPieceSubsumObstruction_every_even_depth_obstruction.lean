-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_every_even_depth_obstruction
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.every_even_depth_obstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:12:46.803177+00:00
-- url     : https://prove2.me/theorems/d8ebdc96-7166-4c1c-8e01-89534d2e80dc
-- title:
--   BDL26 Original Piece Subsum Obstruction: every even depth obstruction
-- statement:
--   The BDL26 Original Piece Subsum Obstruction construction uses the every even depth obstruction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L262-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L262-L274

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.every_even_depth_obstruction (S : OddScale) (k : Nat) (hk : 2 ≤ k) :
    2*(k-2)+4 = 2*k ∧
    ∃ p : FamilyZ S (2*(k-2)+4) (TopIndex (2*(k-2)+4)),
    ∃ hp : (upperSyndrome S (k-2)).val p ≠ 0,
      ∀ A : Finset (Fin (topOutput S (k-2)).localComponents.length),
        maskWord (upperRegion S (k-2) (canonicalComponent S (k-2) p hp))
            (upperSyndrome S (k-2)).val +
          (indexedFamily S (2*(k-2)+4)).coboundary1 (TopIndex (2*(k-2)+4))
            (topPieceSubsum S (k-2) A) ≠
        ((indexedDecoderData S (2*(k-2)+4)).selectedMap ⟨2*(k-2)+3, by omega⟩).map2
          (maskWord (lowerRegion S (k-2) (canonicalComponent S (k-2) p hp))
            (topOutput S (k-2)).coarse.val) := by sorry
