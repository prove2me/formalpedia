-- Prove2me | Theorems.Thm_PI_BeDiagZp_coeff_pow_mul_pow_eq_zero_of_lt
-- name    : PI.BeDiagZp.coeff_pow_mul_pow_eq_zero_of_lt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:16.197603+00:00
-- url     : https://prove2.me/theorems/0d4a57ef-cc3a-50ca-9da9-531c773eba9c
-- title:
--   Be Diag Zp: coeff pow mul pow eq zero of lt
-- statement:
--   The Be Diag Zp construction uses the coeff pow mul pow eq zero of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L67-L76

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

theorem PI.BeDiagZp.coeff_pow_mul_pow_eq_zero_of_lt {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) {m j : ℕ} {α : σ →₀ ℕ} (h : Finsupp.degree α < m + j) :
    coeff α (x ^ m * y ^ j) = 0 := by sorry
