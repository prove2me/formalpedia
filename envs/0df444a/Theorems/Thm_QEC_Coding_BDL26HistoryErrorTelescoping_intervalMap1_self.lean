-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap1_self
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap1_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:26:56.376205+00:00
-- url     : https://prove2.me/theorems/341df78b-6ab4-4aad-91d8-53308f87cd0a
-- title:
--   BDL26 History Error Telescoping: interval Map1 self
-- statement:
--   The BDL26 History Error Telescoping construction uses the interval Map1 self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L107-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L107-L109

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder
open scoped Classical
universe u v
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap1_self (D : BDL26DecoderData depth C0 C1 C2)
    (a : LevelIndex depth) : intervalMap1 D a a (Nat.le_refl _) = LinearMap.id := by sorry
