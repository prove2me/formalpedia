-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_accumulatedPotential_comp
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T12:48:54.373527+00:00
-- url     : https://prove2.me/theorems/3643fe28-8dbb-49a3-a805-df9a37bdd58e
-- title:
--   BDL26 History Error Telescoping: accumulated Potential comp
-- statement:
--   The BDL26 History Error Telescoping construction uses the accumulated Potential comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L174-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L174-L230

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_comp (upper : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 upper) (c : Nat) (hc : c ≤ upper.val)
    (b a : LevelIndex n) (hbc : b.val ≤ c) (hab : a.val ≤ b.val) :
    accumulatedPotential S n upper u a c hc (hab.trans hbc) =
      intervalMap0 (SuffixData S n) b
          ⟨c,Nat.lt_succ_of_le (hc.trans (Nat.le_of_lt_succ upper.isLt))⟩ hbc
          (accumulatedPotential S n upper u a b.val (hbc.trans hc) hab) +
        accumulatedPotential S n upper u b c hc hbc := by sorry
