-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_intervalPotential_sum
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.intervalPotential_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:17:54.169055+00:00
-- url     : https://prove2.me/theorems/8f4d8cef-30c0-43b5-b117-d08862c228aa
-- title:
--   BDL26 Localized History Error Descent: interval Potential sum
-- statement:
--   Explicit full-sum interface, including every original interior level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L430-L433
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L430-L433

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.intervalPotential_sum (a b : LevelIndex n) :
    intervalPotential S n sigma tau top a b=
      ∑ i : StepIndex n, (if h : a.val< (i.succ).val ∧ (i.succ).val≤b.val then
        intervalMap0 (Data S n) i.succ b h.2 (edgePotential S n sigma tau top i) else 0) := by sorry
