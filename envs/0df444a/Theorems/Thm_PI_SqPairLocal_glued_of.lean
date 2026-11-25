-- Prove2me | Theorems.Thm_PI_SqPairLocal_glued_of
-- name    : PI.SqPairLocal.glued_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:23:52.040493+00:00
-- url     : https://prove2.me/theorems/2299eec0-62d6-58db-b273-e73b4ac16280
-- title:
--   Sq Pair Local: glued of
-- statement:
--   The Sq Pair Local construction uses the glued of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L255-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SqPairLocalOfSteps.lean#L255-L263

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem PI.SqPairLocal.glued_of (hG : Glue) (hS : SplitPlace) (hI : InertPlace) : Glued := by sorry
