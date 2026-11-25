-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Cont_continuous_evalV
-- name    : PI.LevelKSplit.W.Cont.continuous_evalV
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:35:35.996398+00:00
-- url     : https://prove2.me/theorems/f754ff79-69ea-5cde-ab65-33ff7153c6da
-- title:
--   Cont: continuous eval V
-- statement:
--   The Cont construction uses the continuous eval V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousAtPlace.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousAtPlace.lean#L15-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ContinuousAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Cont
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem PI.LevelKSplit.W.Cont.continuous_evalV (v : HeightOneSpectrum (𝓞 F)) : Continuous (evalV F v) := by sorry
