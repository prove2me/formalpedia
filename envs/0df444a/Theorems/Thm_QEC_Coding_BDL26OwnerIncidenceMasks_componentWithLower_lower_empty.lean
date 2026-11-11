-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_componentWithLower_lower_empty
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.componentWithLower_lower_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:13:44.337212+00:00
-- url     : https://prove2.me/theorems/b48ae330-8c68-4897-83b5-3bd76c8f1387
-- title:
--   BDL26 Owner Incidence Masks: component With Lower lower empty
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the component With Lower lower empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L73-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L73-L82

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.componentWithLower_lower_empty (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    lowerOwnerMaskRegion (componentWithLower lower p hp) = ∅ := by sorry
