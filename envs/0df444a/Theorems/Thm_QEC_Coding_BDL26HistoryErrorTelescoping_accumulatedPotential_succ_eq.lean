-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_accumulatedPotential_succ_eq
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_succ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:09:37.196571+00:00
-- url     : https://prove2.me/theorems/6ad5d861-b0f1-45a3-b0e0-d85f95e347a3
-- title:
--   BDL26 History Error Telescoping: accumulated Potential succ eq
-- statement:
--   The BDL26 History Error Telescoping construction uses the accumulated Potential succ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L144-L154
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L144-L154

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_succ_eq (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b) (a : LevelIndex n)
    (c : Nat) (hc : c+1 ≤ b.val) (ha : a.val ≤ c+1) :
    accumulatedPotential S n b u a (c+1) hc ha =
      if h : a.val = c+1 then 0 else
        let i : StepIndex n := ⟨c,Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self c) hc) (Nat.le_of_lt_succ b.isLt)⟩
        ((SuffixData S n).selectedMap i).map0
          (accumulatedPotential S n b u a c (by omega) (by omega)) +
            descentPotential S n b u i (by change c < b.val; omega) := by sorry
