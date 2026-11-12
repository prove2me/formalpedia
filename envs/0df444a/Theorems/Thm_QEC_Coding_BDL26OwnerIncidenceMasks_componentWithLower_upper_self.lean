-- Prove2me | Theorems.Thm_QEC_Coding_BDL26OwnerIncidenceMasks_componentWithLower_upper_self
-- name    : QEC.Coding.BDL26OwnerIncidenceMasks.componentWithLower_upper_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:15:52.226052+00:00
-- url     : https://prove2.me/theorems/461a33a2-ddf7-421a-bc35-69190d9b21be
-- title:
--   BDL26 Owner Incidence Masks: component With Lower upper self
-- statement:
--   The BDL26 Owner Incidence Masks construction uses the component With Lower upper self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L84-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/HistoryComponentMask.lean#L84-L90

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryWitness
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_HistoryComponentMask
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26OwnerIncidenceMasks
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26OwnerIncidenceMasks.componentWithLower_upper_self (lower : Finset StrictLowerNode)
    (p : FamilyZ scaleFive 4 (4 : LevelIndex 4)) (hp : witnessUpper.val p ≠ 0) :
    p ∈ upperOwnerMaskRegion (componentWithLower lower p hp) := by sorry
