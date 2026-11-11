-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_linearUp_comp
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.linearUp_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:47:06.024206+00:00
-- url     : https://prove2.me/theorems/d4a29875-d61d-44ae-8c52-246ad2b473e7
-- title:
--   BDL26 History Error Telescoping: linear Up comp
-- statement:
--   The BDL26 History Error Telescoping construction uses the linear Up comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L60-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L60-L83

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.linearUp_comp
    (edge : ∀ i : StepIndex depth, V i.castSucc →ₗ[BDL26Field] V i.succ)
    (c : Nat) (hc : c ≤ depth) (b a : LevelIndex depth)
    (hbc : b.val ≤ c) (hab : a.val ≤ b.val) :
    linearUp edge c hc a (hab.trans hbc) =
      (linearUp edge c hc b hbc).comp
        (linearUp edge b.val (Nat.le_of_lt_succ b.isLt) a hab) := by sorry
