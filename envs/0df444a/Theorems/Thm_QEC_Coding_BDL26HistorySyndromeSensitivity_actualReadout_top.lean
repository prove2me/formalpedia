-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualReadout_top
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.actualReadout_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T10:58:25.796486+00:00
-- url     : https://prove2.me/theorems/0ec4447f-f0d2-42fd-a1c8-7adadda62548
-- title:
--   BDL26 History Syndrome Sensitivity: actual Readout top
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the actual Readout top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L84-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L84-L86

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Preimages
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26RXCoarseInfluence BDL26RXInfluenceBounds MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (d : Nat) (i : StepIndex d)
variable (n : Nat)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.actualReadout_top (sigma : TopInput S n) :
    actualReadout S n sigma (TopIndex n) = sigma.val := by sorry
