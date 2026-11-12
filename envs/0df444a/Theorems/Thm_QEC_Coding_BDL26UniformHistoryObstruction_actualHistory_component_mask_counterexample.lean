-- Prove2me | Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_actualHistory_component_mask_counterexample
-- name    : QEC.Coding.BDL26UniformHistoryObstruction.actualHistory_component_mask_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:02:13.9262+00:00
-- url     : https://prove2.me/theorems/ad289181-4e24-45f0-b533-f4ca0a877078
-- title:
--   BDL26 Uniform History Obstruction: actual History component mask counterexample
-- statement:
--   Uniform failure on the actual recovered coarse word, for every strictly-lower marking.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformComponentMask.lean#L104-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/UniformComponentMask.lean#L104-L133

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformIsolation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformComponentMask
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26UniformHistoryObstruction
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26UniformHistoryObstruction.actualHistory_component_mask_counterexample (S : OddScale) (j : Nat)
    (lower : Finset (StrictLowerNode S j)) :
    ∃ p : FamilyZ S (2 * j + 4) (TopIndex (2 * j + 4)),
    ∃ hp : (upperSyndrome S j).val p ≠ 0,
      maskWord (upperRegion S j (component S j lower p hp))
        (((indexedDecoderData S (2 * j + 4)).selectedMap ⟨2 * j + 3, by omega⟩).map2
          (topOutput S j).coarse.val) ≠
      ((indexedDecoderData S (2 * j + 4)).selectedMap ⟨2 * j + 3, by omega⟩).map2
        (maskWord (lowerRegion S j (component S j lower p hp)) (topOutput S j).coarse.val) := by sorry
