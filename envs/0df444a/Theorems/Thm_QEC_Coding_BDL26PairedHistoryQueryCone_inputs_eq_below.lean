-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_inputs_eq_below
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.inputs_eq_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:06:48.300144+00:00
-- url     : https://prove2.me/theorems/34c08655-93f9-409e-8076-1ff45e913207
-- title:
--   BDL26 Paired History Query Cone: inputs eq below
-- statement:
--   Determinism of the unchanged lower suffix after actual input coalescence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L488-L491
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L488-L491

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26PairedHistoryQueryCone.inputs_eq_below (s t : TopInput S n) (a b : LevelIndex n)
    (ha : b.val ≤ a.val) (hs : actualInputs S n s a = actualInputs S n t a) :
    actualInputs S n s b = actualInputs S n t b := by sorry
