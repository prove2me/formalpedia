-- Prove2me | Theorems.Thm_PI_BeDiagZp_coeff_expT_add
-- name    : PI.BeDiagZp.coeff_expT_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:05.420877+00:00
-- url     : https://prove2.me/theorems/0f87119c-267e-4064-a072-b1b8d5909750
-- title:
--   Be Diag Zp: coeff exp T add
-- statement:
--   The Be Diag Zp construction uses the coeff exp T add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L122-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L122-L132

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

theorem PI.BeDiagZp.coeff_expT_add {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) {α : σ →₀ ℕ} {N : ℕ} (hN : Finsupp.degree α < N) :
    coeff α (expT (x + y) N) = coeff α (expT x N * expT y N) := by sorry
