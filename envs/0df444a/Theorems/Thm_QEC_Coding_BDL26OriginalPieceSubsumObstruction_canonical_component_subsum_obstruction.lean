-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OriginalPieceSubsumObstruction_canonical_component_subsum_obstruction
-- name    : QEC.Coding.BDL26OriginalPieceSubsumObstruction.canonical_component_subsum_obstruction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:04:43.894729+00:00
-- url     : https://prove2.me/theorems/8c84d97b-52bb-48d6-a50e-c565a1de7f8d
-- title:
--   BDL26 Original Piece Subsum Obstruction: canonical component subsum obstruction
-- statement:
--   Primitive inputs are only S,j. The one actual component defeats every subsum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L246-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/OriginalPieceSubsumObstruction.lean#L246-L260

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Consistency
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_OriginalPieceSubsumObstruction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OriginalPieceSubsumObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26UniformHistoryObstruction MultiscaleDecoder
open scoped Classical BigOperators

theorem QEC.Coding.BDL26OriginalPieceSubsumObstruction.canonical_component_subsum_obstruction (S : OddScale) (j : Nat) :
    ∃ p : FamilyZ S (2*j+4) (TopIndex (2*j+4)),
    ∃ hp : (upperSyndrome S j).val p ≠ 0,
      ∀ A : Finset (Fin (topOutput S j).localComponents.length),
        maskWord (upperRegion S j (canonicalComponent S j p hp)) (upperSyndrome S j).val +
          (indexedFamily S (2*j+4)).coboundary1 (TopIndex (2*j+4))
            (topPieceSubsum S j A) ≠
        ((indexedDecoderData S (2*j+4)).selectedMap ⟨2*j+3, by omega⟩).map2
          (maskWord (lowerRegion S j (canonicalComponent S j p hp))
            (topOutput S j).coarse.val) := by sorry
