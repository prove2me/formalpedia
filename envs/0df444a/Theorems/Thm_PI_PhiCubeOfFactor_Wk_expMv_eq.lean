-- Prove2me | Theorems.Thm_PI_PhiCubeOfFactor_Wk_expMv_eq
-- name    : PI.PhiCubeOfFactor.Wk.expMv_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:35:52.352683+00:00
-- url     : https://prove2.me/theorems/42640f2f-6730-439e-bd1a-e61747b72ecb
-- title:
--   Wk: exp Mv eq
-- statement:
--   The Wk construction uses the exp Mv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFactorIdentity/ExpMvEq.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFactorIdentity/ExpMvEq.lean#L14-L14

import Definitions.Def_Formalism_PeriodIntegrals_PhiCubeOfFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFactorIdentity_ExpMvEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PhiCubeOfFactor PI.PhiCubeOfFactor.Wk
open PI.PhiCubeOfFactor MvPowerSeries PI.FglShared
variable {p : ℕ} [Fact p.Prime]

theorem PI.PhiCubeOfFactor.Wk.expMv_eq {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : expMv F = PI.FglPhSplit.expMv F := by sorry
