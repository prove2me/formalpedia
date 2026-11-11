-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_descentWord_step
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.descentWord_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:21:56.539208+00:00
-- url     : https://prove2.me/theorems/7d714434-333b-419f-860d-fce94a404d94
-- title:
--   BDL26 History Error Telescoping: descent Word step
-- statement:
--   The BDL26 History Error Telescoping construction uses the descent Word step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L98-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping.lean#L98-L118

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.descentWord_step (sigma : TopInput S n) (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b)
    (hu : (SuffixData S n).family.coboundary1 b u = actualReadout S n sigma b)
    (i : StepIndex n) (hi : i.val < b.val) :
    ((SuffixData S n).selectedMap i).map1
        (descentWord S n b u i.castSucc (by change i.val ≤ b.val; omega)) =
      descentWord S n b u i.succ (by change i.val+1 ≤ b.val; omega) +
        (actualOutput S n sigma i).correction +
        (SuffixData S n).family.coboundary0 i.succ (descentPotential S n b u i hi) := by sorry
