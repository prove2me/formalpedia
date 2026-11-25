-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_SimeqPdInt_int_pderiv
-- name    : PI.UnitaryGroupMassFormula.SimeqPdInt.int_pderiv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:14.217011+00:00
-- url     : https://prove2.me/theorems/a4c4d5f6-1f97-4084-9bae-6e0ff9e11fe6
-- title:
--   Simeq Pd Int: int pderiv
-- statement:
--   The Simeq Pd Int construction uses the int pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L66-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialCoefficientSeries/CoeffExpMvEqTs.lean#L66-L75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SimeqPdInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CubeFormalIdentities_CoeffPowMulPowEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialCoefficientSeries_CoeffExpMvEqTs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SimeqPdInt
variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem PI.UnitaryGroupMassFormula.SimeqPdInt.int_pderiv (k : σ) {F : MvPowerSeries σ ℂ_[p]} (hF : PI.FglGram.IntegralMv F) :
    PI.FglGram.IntegralMv (pderiv ℂ_[p] k F) := by sorry
