-- Prove2me | Theorems.Thm_PI_CubicExponentialFactor_Wk_expMv_addC
-- name    : PI.CubicExponentialFactor.Wk.expMv_addC
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:27:03.823086+00:00
-- url     : https://prove2.me/theorems/71843f5d-b866-5413-bdd0-142fa1226a34
-- title:
--   Wk: exp Mv add C
-- statement:
--   The Wk construction uses the exp Mv add C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubicExponentialFactor/ExpMvAddC.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CubicExponentialFactor/ExpMvAddC.lean#L19-L21

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

theorem PI.CubicExponentialFactor.Wk.expMv_addC {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) : expMv (f + g) = expMv f * expMv g := by sorry
