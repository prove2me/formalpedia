-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_not_actualHistory_component_mask_commutation
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.not_actualHistory_component_mask_commutation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:14:59.702993+00:00
-- url     : https://prove2.me/theorems/c0f45d20-3f6d-4c77-80c8-d973c80048b0
-- title:
--   BDL26 Owner Incidence Masks: not actual History component mask commutation
-- statement:
--   Negation of the universal component-mask equation required by the
--   unconditional owner/component coherence route.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L119-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L119-L127

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.not_actualHistory_component_mask_commutation (lower : Finset StrictLowerNode) :
    ¬ (∀ (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0),
      maskWord (upperOwnerMaskRegion (componentWithLower lower p hp))
        (((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2 witnessTopOutput.coarse.val) =
      ((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2
        (maskWord (lowerOwnerMaskRegion (componentWithLower lower p hp)) witnessTopOutput.coarse.val)) := by sorry
