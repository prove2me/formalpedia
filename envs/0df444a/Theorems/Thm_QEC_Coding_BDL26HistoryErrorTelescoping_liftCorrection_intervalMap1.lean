-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_liftCorrection_intervalMap1
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.liftCorrection_intervalMap1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:09:29.095685+00:00
-- url     : https://prove2.me/theorems/0992da68-e316-43bf-9e7d-bf2e45c59a38
-- title:
--   BDL26 History Error Telescoping: lift Correction interval Map1
-- statement:
--   Interval lifting is exactly the old full correction lift, not merely
--   an alternative word with the same syndrome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L184-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L184-L208

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.liftCorrection_intervalMap1 (D : BDL26DecoderData depth C0 C1 C2)
    (b : Nat) (hb : b ≤ depth) (a : LevelIndex depth) (ha : a.val ≤ b)
    (w : D.family.Cochain1 a) :
    liftCorrection D ⟨b,Nat.lt_succ_of_le hb⟩
      (intervalMap1 D a ⟨b,Nat.lt_succ_of_le hb⟩ ha w) = liftCorrection D a w := by sorry
