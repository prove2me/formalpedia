-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_depthTwo_readout
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.depthTwo_readout
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T11:32:40.17212+00:00
-- url     : https://prove2.me/theorems/a76545c5-5fe1-41b5-93aa-ab1047a16432
-- title:
--   BDL26 History Syndrome Sensitivity: depth Two readout
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the depth Two readout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L122-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity.lean#L122-L123

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.depthTwo_readout (sigma : TopInput S 0) : actualReadout S 0 sigma 0 = sigma.val := by sorry
