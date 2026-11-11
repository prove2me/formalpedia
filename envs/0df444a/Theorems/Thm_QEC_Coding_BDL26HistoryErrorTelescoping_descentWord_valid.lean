-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_descentWord_valid
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.descentWord_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:08:20.875261+00:00
-- url     : https://prove2.me/theorems/7be78b69-6025-42ae-b6ef-b3862af707df
-- title:
--   BDL26 History Error Telescoping: descent Word valid
-- statement:
--   The BDL26 History Error Telescoping construction uses the descent Word valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L72-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L72-L81

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.descentWord_valid (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (a : LevelIndex n) (ha : a.val ≤ b.val) :
    (SuffixData S n).family.coboundary1 a (descentWord S n b u a ha) =
      (actualInputs S n sigma a).val := by sorry
