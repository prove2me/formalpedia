-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_interval_facts_nat
-- name    : QEC.Coding.BDL26HistoryLogicalResidual.interval_facts_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:11:22.440163+00:00
-- url     : https://prove2.me/theorems/9e34b3b0-910b-4edb-b519-9a34d8f949be
-- title:
--   BDL26 History Logical Residual: interval facts nat
-- statement:
--   Word and quotient equations are proved together along the actual interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L101-L138
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryLogicalResidual/Intervals.lean#L101-L138

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LogicalQubitPreservation
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryLogicalResidual_Intervals
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryLogicalResidual
open MultiscaleDecoder BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RZMap1CoordinateBridge
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryLogicalResidual.interval_facts_nat (b : Nat) (hb : b ≤ n) (a : LevelIndex n) (ha : a.val ≤ b)
    (w : FC.Cocycle S (a.val+2)) :
    (intervalCocycle S n a ⟨b,Nat.lt_succ_of_le hb⟩ ha w).val =
        intervalMap1 (SuffixData S n) a ⟨b,Nat.lt_succ_of_le hb⟩ ha w.val ∧
      suffixEquiv S n a ⟨b,Nat.lt_succ_of_le hb⟩ (FC.classOf S (a.val+2) w) =
        FC.classOf S (b+2) (intervalCocycle S n a ⟨b,Nat.lt_succ_of_le hb⟩ ha w) := by sorry
