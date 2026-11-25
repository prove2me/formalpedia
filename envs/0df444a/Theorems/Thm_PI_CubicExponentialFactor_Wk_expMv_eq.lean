-- Prove2me | Theorems.Thm_PI_CubicExponentialFactor_Wk_expMv_eq
-- name    : PI.CubicExponentialFactor.Wk.expMv_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:27:37.29732+00:00
-- url     : https://prove2.me/theorems/681723bc-3571-445a-bd19-188f35fef578
-- title:
--   Wk: exp Mv eq
-- statement:
--   The Wk construction uses the exp Mv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubicExponentialFactor/ExpMvAddC.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubicExponentialFactor/ExpMvAddC.lean#L17-L17

import Definitions.Def_Formalism_PeriodIntegrals_CubicExponentialFactor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_CoeffSingleLg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_NormAddLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubicExponentialFactor_ExpMvAddC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CubicExponentialFactor PI.CubicExponentialFactor.Wk
open PI.CubicExponentialFactor MvPowerSeries PI.FglShared
set_option linter.unusedSimpArgs false
variable {p : ℕ} [Fact p.Prime]

theorem PI.CubicExponentialFactor.Wk.expMv_eq {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : expMv F = PI.FglPhSplit.expMv F := by sorry
