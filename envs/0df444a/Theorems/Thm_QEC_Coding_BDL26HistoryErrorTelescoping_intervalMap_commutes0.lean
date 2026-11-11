-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalMap_commutes0
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap_commutes0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:27:20.377205+00:00
-- url     : https://prove2.me/theorems/f33e82ad-5fe3-4ec6-8299-99851294296f
-- title:
--   BDL26 History Error Telescoping: interval Map commutes0
-- statement:
--   The whole degree-zero potential commutes through every actual interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L148-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/Intervals.lean#L148-L180

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.intervalMap_commutes0 (D : BDL26DecoderData depth C0 C1 C2)
    (b : Nat) (hb : b ≤ depth) (a : LevelIndex depth) (ha : a.val ≤ b)
    (p : D.family.Cochain0 a) :
    D.family.coboundary0 ⟨b,Nat.lt_succ_of_le hb⟩
        (intervalMap0 D a ⟨b,Nat.lt_succ_of_le hb⟩ ha p) =
      intervalMap1 D a ⟨b,Nat.lt_succ_of_le hb⟩ ha (D.family.coboundary0 a p) := by sorry
