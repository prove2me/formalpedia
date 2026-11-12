-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_component_subsum_obstruction
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.component_subsum_obstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:04:30.627621+00:00
-- url     : https://prove2.me/theorems/bab7dcd4-18ab-4f10-92e5-0295abc8029d
-- title:
--   BDL26 Original Piece Subsum Obstruction: component subsum obstruction
-- statement:
--   The same active coordinate refutes every choice of original correction pieces.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L105-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L105-L130

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.component_subsum_obstruction (S : OddScale) (j : Nat)
    (lower : Finset (StrictLowerNode S j)) :
    ∃ p : FamilyZ S (2*j+4) (TopIndex (2*j+4)),
    ∃ hp : (upperSyndrome S j).val p ≠ 0,
      ∀ A : Finset (Fin (topOutput S j).localComponents.length),
        maskWord (upperRegion S j (component S j lower p hp)) (upperSyndrome S j).val +
          (indexedFamily S (2*j+4)).coboundary1 (TopIndex (2*j+4))
            (topPieceSubsum S j A) ≠
        ((indexedDecoderData S (2*j+4)).selectedMap ⟨2*j+3, by omega⟩).map2
          (maskWord (lowerRegion S j (component S j lower p hp))
            (topOutput S j).coarse.val) := by sorry
