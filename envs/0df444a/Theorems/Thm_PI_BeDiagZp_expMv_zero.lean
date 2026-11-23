-- Prove2me | Theorems.Thm_PI_BeDiagZp_expMv_zero
-- name    : PI.BeDiagZp.expMv_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:15:37.775856+00:00
-- url     : https://prove2.me/theorems/99f1ccfe-c6c9-414e-8d9a-5d8b6168e4c1
-- title:
--   Be Diag Zp: exp Mv zero
-- statement:
--   The Be Diag Zp construction uses the exp Mv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L146-L149

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
open IntegralPowerSeriesBall
variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem PI.BeDiagZp.expMv_zero : expMv (0 : MvPowerSeries σ ℂ_[p]) = 1 := by sorry
