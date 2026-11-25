-- Prove2me | Theorems.Thm_PI_BeDiagZp_inv_fact_mul_choose
-- name    : PI.BeDiagZp.inv_fact_mul_choose
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:43.070733+00:00
-- url     : https://prove2.me/theorems/08a405cc-95d9-4619-ae4c-a3ffe32aeab3
-- title:
--   Be Diag Zp: inv fact mul choose
-- statement:
--   The Be Diag Zp construction uses the inv fact mul choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L87-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L87-L97

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

theorem PI.BeDiagZp.inv_fact_mul_choose (n m : ℕ) (h : m ≤ n) :
    (n.factorial : ℂ_[p])⁻¹ * (n.choose m : ℂ_[p]) =
      (m.factorial : ℂ_[p])⁻¹ * ((n - m).factorial : ℂ_[p])⁻¹ := by sorry
