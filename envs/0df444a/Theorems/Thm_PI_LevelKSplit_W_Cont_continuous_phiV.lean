-- Prove2me | Theorems.Thm_PI_LevelKSplit_W_Cont_continuous_phiV
-- name    : PI.LevelKSplit.W.Cont.continuous_phiV
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:34:48.55781+00:00
-- url     : https://prove2.me/theorems/017318d6-130f-5b78-bc64-c9b77b36b9e3
-- title:
--   Cont: continuous phi V
-- statement:
--   The Cont construction uses the continuous phi V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousAtPlace.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/ContinuousAtPlace.lean#L33-L38

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

theorem PI.LevelKSplit.W.Cont.continuous_phiV (v : HeightOneSpectrum (𝓞 F)) : Continuous (phiV (E := E) v) := by sorry
