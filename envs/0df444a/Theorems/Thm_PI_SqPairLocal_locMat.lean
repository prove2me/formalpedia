-- Prove2me | Theorems.Thm_PI_SqPairLocal_locMat
-- name    : PI.SqPairLocal.locMat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:25:08.923491+00:00
-- url     : https://prove2.me/theorems/597dec17-7a14-56c2-ae01-c2ef4bb59c51
-- title:
--   Sq Pair Local: loc Mat
-- statement:
--   The Sq Pair Local construction uses the loc Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/Imports.lean#L68-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/Imports.lean#L68-L273

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IntAtOfDivAtZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_Imports
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
open PI.SqPair
attribute [local instance] StModel.cr StModel.dom StModel.dvr StModel.hens StModel.fin

theorem PI.SqPairLocal.locMat : LocMat := by sorry
