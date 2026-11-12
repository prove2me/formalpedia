-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_actualHistory_component_mask_counterexample
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.actualHistory_component_mask_counterexample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:13:57.867143+00:00
-- url     : https://prove2.me/theorems/9a269304-9e73-4625-90c0-33c18be03b6c
-- title:
--   BDL26 Owner Incidence Masks: actual History component mask counterexample
-- statement:
--   For every possible lower marking, the actual top connected component
--   violates the selected-map2 mask equation on the actual recovered syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L94-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L94-L115

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.actualHistory_component_mask_counterexample (lower : Finset StrictLowerNode) :
    ∃ p : FamilyZ scaleFive 4 (4 : LevelIndex 4), ∃ hp : witnessUpper.val p ≠ 0,
      maskWord (upperOwnerMaskRegion (componentWithLower lower p hp))
        (((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2 witnessTopOutput.coarse.val) ≠
      ((indexedDecoderData scaleFive 4).selectedMap (3 : StepIndex 4)).map2
        (maskWord (lowerOwnerMaskRegion (componentWithLower lower p hp)) witnessTopOutput.coarse.val) := by sorry
