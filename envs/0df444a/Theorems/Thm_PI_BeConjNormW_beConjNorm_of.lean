-- Prove2me | Theorems.Thm_PI_BeConjNormW_beConjNorm_of
-- name    : PI.BeConjNormW.beConjNorm_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:24:55.491548+00:00
-- url     : https://prove2.me/theorems/9b9b5527-1597-4cf0-86e6-76d1f8a8dec6
-- title:
--   Be Conj Norm W: be Conj Norm of
-- statement:
--   The Be Conj Norm W construction uses the be Conj Norm of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateNormBound/Development.lean#L40-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ConjugateNormBound/Development.lean#L40-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BeConjNorm
import Definitions.Def_Formalism_PeriodIntegrals_PhNormUnits
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PowerSeriesNormUnits_NormUnitsOfCalculation
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ConjugateNormBound_Development
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
open PI PI.BeConjNormW
open PI.PhNormUnits

theorem PI.BeConjNormW.beConjNorm_of (h : StepCore) : PI.BeConjNorm.BeConjNorm := by sorry
