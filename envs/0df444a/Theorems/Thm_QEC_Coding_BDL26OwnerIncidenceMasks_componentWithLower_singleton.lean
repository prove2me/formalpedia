-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_componentWithLower_singleton
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.componentWithLower_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:28:24.778308+00:00
-- url     : https://prove2.me/theorems/b8ed3c51-3334-4d0b-8e36-1fdff5501d55
-- title:
--   BDL26 Owner Incidence Masks: component With Lower singleton
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the component With Lower singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L56-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L56-L63

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.componentWithLower_singleton (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    componentWithLower lower p hp = {BDL26TopOwnerIsolation.topNode (witnessTopOwner p)} := by sorry
