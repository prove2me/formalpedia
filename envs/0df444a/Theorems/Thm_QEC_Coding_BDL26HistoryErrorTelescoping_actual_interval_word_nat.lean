-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actual_interval_word_nat
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.actual_interval_word_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:23:11.971637+00:00
-- url     : https://prove2.me/theorems/31cdef48-84c6-4533-8fab-26248823efa7
-- title:
--   BDL26 History Error Telescoping: actual interval word nat
-- statement:
--   The BDL26 History Error Telescoping construction uses the actual interval word nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L232-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L232-L291

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.actual_interval_word_nat (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (c : Nat) (hc : c ≤ b.val) (a : LevelIndex n) (ha : a.val ≤ c) :
    intervalMap1 (SuffixData S n) a
        ⟨c,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ b.isLt))⟩ ha
        (descentWord S n b u a (ha.trans hc)) =
      descentWord S n b u ⟨c,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ b.isLt))⟩ hc +
        correctionIntervalSum S n sigma a
          ⟨c,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ b.isLt))⟩ +
        (SuffixData S n).family.coboundary0 _ (accumulatedPotential S n b u a c hc ha) := by sorry
