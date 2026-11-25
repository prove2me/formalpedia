-- Prove2me | Theorems.Thm_PI_BeDiagZp_expT_mul_expT
-- name    : PI.BeDiagZp.expT_mul_expT
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:27.606043+00:00
-- url     : https://prove2.me/theorems/b534486d-2992-440f-b517-b4e5fc2e8ac4
-- title:
--   Be Diag Zp: exp T mul exp T
-- statement:
--   The Be Diag Zp construction uses the exp T mul exp T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L114-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L114-L120

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

theorem PI.BeDiagZp.expT_mul_expT (x y : MvPowerSeries σ ℂ_[p]) (N : ℕ) :
    expT x N * expT y N = ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (((m.factorial : ℂ_[p])⁻¹ * (j.factorial : ℂ_[p])⁻¹) • (x ^ m * y ^ j)) := by sorry
