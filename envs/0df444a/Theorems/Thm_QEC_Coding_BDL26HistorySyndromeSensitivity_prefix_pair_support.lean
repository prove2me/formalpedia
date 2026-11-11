-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_prefix_pair_support
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.prefix_pair_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:04:38.064322+00:00
-- url     : https://prove2.me/theorems/0c465e62-9c2b-43e9-82ab-7a7c75905635
-- title:
--   BDL26 History Syndrome Sensitivity: prefix pair support
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the prefix pair support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L139-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L139-L169

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.prefix_pair_support (b : Nat) (hb : b ≤ n)
    (sigma tau : (SuffixData S n).family.Syndrome ⟨b,Nat.lt_succ_of_le hb⟩)
    (a : LevelIndex n) (ha : a.val ≤ b) :
    hammingSupport
      ((prefixInput (SuffixData S n) (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n))
          b hb sigma a ha).val +
        (prefixInput (SuffixData S n) (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n))
          b hb tau a ha).val) ⊆
      propagate S n b hb a ha (hammingSupport (sigma.val + tau.val)) := by sorry
