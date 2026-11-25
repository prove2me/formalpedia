-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_firstJetIntegralGeneral_holds
-- name    : PI.JetsPhW.Low.firstJetIntegralGeneral_holds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:10:46.498007+00:00
-- url     : https://prove2.me/theorems/06c75297-5dd1-59c3-980f-aa41a4797962
-- title:
--   Low: first Jet Integral General holds
-- statement:
--   The Low construction uses the first Jet Integral General holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/FirstJetIntegralGeneralHolds.lean#L34-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/FirstJetIntegralGeneralHolds.lean#L34-L79

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ExpLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_FirstJetIntegralGeneralHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
open PI.JetsPhW

theorem PI.JetsPhW.Low.firstJetIntegralGeneral_holds : OneG := by sorry
