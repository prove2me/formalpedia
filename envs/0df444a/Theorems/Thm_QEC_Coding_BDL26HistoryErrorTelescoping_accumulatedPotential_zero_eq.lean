-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_accumulatedPotential_zero_eq
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_zero_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:09:51.35258+00:00
-- url     : https://prove2.me/theorems/688400d8-94eb-47cf-a1fc-b171e95e6b6d
-- title:
--   BDL26 History Error Telescoping: accumulated Potential zero eq
-- statement:
--   The BDL26 History Error Telescoping construction uses the accumulated Potential zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L139-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L139-L142

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_zero_eq (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b) (a : LevelIndex n) (ha : a.val ≤ 0) :
    accumulatedPotential S n b u a 0 (Nat.zero_le _) ha = 0 := by sorry
