-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_linearUp_succ
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.linearUp_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:39:32.36659+00:00
-- url     : https://prove2.me/theorems/df5ac61c-ade2-468b-b001-2301c05344e7
-- title:
--   BDL26 History Error Telescoping: linear Up succ
-- statement:
--   The BDL26 History Error Telescoping construction uses the linear Up succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L51-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L51-L58

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder
open scoped Classical
universe u v
variable {depth : Nat} {V : LevelIndex depth → Type u}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module BDL26Field (V i)]

theorem QEC.Coding.BDL26HistoryErrorTelescoping.linearUp_succ
    (edge : ∀ i : StepIndex depth, V i.castSucc →ₗ[BDL26Field] V i.succ)
    (b : Nat) (hb : b+1 ≤ depth) (a : LevelIndex depth) (ha : a.val ≤ b) :
    linearUp edge (b+1) hb a (ha.trans (Nat.le_succ b)) =
      (edge ⟨b,by omega⟩).comp (linearUp edge b (by omega) a ha) := by sorry
