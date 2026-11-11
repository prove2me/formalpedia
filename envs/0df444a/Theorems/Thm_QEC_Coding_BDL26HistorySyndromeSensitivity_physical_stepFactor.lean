-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_physical_stepFactor
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.physical_stepFactor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:54:07.989561+00:00
-- url     : https://prove2.me/theorems/cef82a0a-cf95-4cc3-8ffc-218d825bf52f
-- title:
--   BDL26 History Syndrome Sensitivity: physical step Factor
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the physical step Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L106-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L106-L111

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.physical_stepFactor (b : Nat) (hb : b < n) :
    stepFactor (n+2) (LevelTwoHistory.physicalStep (⟨b,hb⟩ : StepIndex n)) =
      if b % 2 = 0 then 57 else 1 := by sorry
