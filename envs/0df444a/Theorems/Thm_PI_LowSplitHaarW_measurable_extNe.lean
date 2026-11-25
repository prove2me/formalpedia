-- Prove2me | Theorems.Thm_PI_LowSplitHaarW_measurable_extNe
-- name    : PI.LowSplitHaarW.measurable_extNe
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:30.614054+00:00
-- url     : https://prove2.me/theorems/34c564b9-eeb4-4386-a8de-ae5b6cf53471
-- title:
--   Low Split Haar W: measurable ext Ne
-- statement:
--   The Low Split Haar W construction uses the measurable ext Ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerShearHaar/MeasurePreservingOfCard.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerShearHaar/MeasurePreservingOfCard.lean#L13-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_MeasurePreservingOfCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
noncomputable section
open PI PI.LowSplitHaarW

theorem PI.LowSplitHaarW.measurable_extNe {ι : Type} [DecidableEq ι] (a : ι) : Measurable (extNe a) := by sorry
