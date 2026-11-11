-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap0_succ
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap0_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:47:38.552089+00:00
-- url     : https://prove2.me/theorems/88af63c3-a9dc-4457-b095-6774ba5cc06c
-- title:
--   BDL26 History Error Telescoping: interval Map0 succ
-- statement:
--   The BDL26 History Error Telescoping construction uses the interval Map0 succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L123-L127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L123-L127

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap0_succ (D : BDL26DecoderData depth C0 C1 C2)
    (a : LevelIndex depth) (i : StepIndex depth) (hai : a.val ≤ i.val) :
    intervalMap0 D a i.succ (by change a.val ≤ i.val+1; omega) =
      ((D.selectedMap i).map0).comp (intervalMap0 D a i.castSucc hai) := by sorry
