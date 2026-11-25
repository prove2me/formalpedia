-- Prove2me | Theorems.Thm_PI_BeDiagZp_IntegralPowerSeriesBall_intMv_one
-- name    : PI.BeDiagZp.IntegralPowerSeriesBall.intMv_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:59.111801+00:00
-- url     : https://prove2.me/theorems/b4f88010-e681-487d-acb7-bb773c9b53c3
-- title:
--   Integral Power Series Ball: int Mv one
-- statement:
--   The Integral Power Series Ball construction uses the int Mv one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L25-L28

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffPowMulPowEqZeroOfLt
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
open PI PI.BeDiagZp
open MvPowerSeries
open PI.BeDiagZp.IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem PI.BeDiagZp.IntegralPowerSeriesBall.intMv_one : IntegralMv (1 : MvPowerSeries σ ℂ_[p]) := by sorry
