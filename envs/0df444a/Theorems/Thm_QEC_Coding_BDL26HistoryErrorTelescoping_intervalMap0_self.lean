-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap0_self
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap0_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:39:41.108033+00:00
-- url     : https://prove2.me/theorems/5e71faca-3d7a-4885-9cd5-052bcd587d8b
-- title:
--   BDL26 History Error Telescoping: interval Map0 self
-- statement:
--   The BDL26 History Error Telescoping construction uses the interval Map0 self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L103-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L103-L105

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap0_self (D : BDL26DecoderData depth C0 C1 C2)
    (a : LevelIndex depth) : intervalMap0 D a a (Nat.le_refl _) = LinearMap.id := by sorry
