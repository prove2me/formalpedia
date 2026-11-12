-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_every_even_depth_counterexample
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.every_even_depth_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:04:23.803274+00:00
-- url     : https://prove2.me/theorems/fb8f2dee-aa95-430e-8a76-fa436d05d11c
-- title:
--   BDL26 Uniform History Obstruction: every even depth counterexample
-- statement:
--   Public internal/API quantifier: every k at least two, with the exact
--   physical-depth equality exposing the subtraction-free construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformComponentMask.lean#L137-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformComponentMask.lean#L137-L149

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformHistoryObstruction.every_even_depth_counterexample (S : OddScale) (k : Nat) (hk : 2 ≤ k) :
    2 * (k - 2) + 4 = 2 * k ∧
    ∀ lower : Finset (StrictLowerNode S (k - 2)),
    ∃ p : FamilyZ S (2 * (k - 2) + 4) (TopIndex (2 * (k - 2) + 4)),
    ∃ hp : (upperSyndrome S (k - 2)).val p ≠ 0,
      maskWord (upperRegion S (k - 2) (component S (k - 2) lower p hp))
        (((indexedDecoderData S (2 * (k - 2) + 4)).selectedMap
          ⟨2 * (k - 2) + 3, by omega⟩).map2 (topOutput S (k - 2)).coarse.val) ≠
      ((indexedDecoderData S (2 * (k - 2) + 4)).selectedMap
        ⟨2 * (k - 2) + 3, by omega⟩).map2
        (maskWord (lowerRegion S (k - 2) (component S (k - 2) lower p hp))
          (topOutput S (k - 2)).coarse.val) := by sorry
