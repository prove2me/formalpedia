-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_phDualGram_main
-- name    : PI.UnitaryGroupMassFormula.PhDualGram.phDualGram_main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:33:37.363674+00:00
-- url     : https://prove2.me/theorems/3731c900-72db-40c2-9f19-f14472112496
-- title:
--   Ph Dual Gram: ph Dual Gram main
-- statement:
--   The Ph Dual Gram construction uses the ph Dual Gram main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/PhDualGramMain.lean#L11-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DualGramSubstitution/PhDualGramMain.lean#L11-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_PhDualGramMain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhDualGram
open PI.FglGram MvPowerSeries

theorem PI.UnitaryGroupMassFormula.PhDualGram.phDualGram_main : PhDualGram := by sorry
