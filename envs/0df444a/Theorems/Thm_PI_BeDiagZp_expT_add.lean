-- Prove2me | Theorems.Thm_PI_BeDiagZp_expT_add
-- name    : PI.BeDiagZp.expT_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:23.472551+00:00
-- url     : https://prove2.me/theorems/7c0d7be3-2434-4f34-97ec-d56ffcb8b401
-- title:
--   Be Diag Zp: exp T add
-- statement:
--   The Be Diag Zp construction uses the exp T add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L99-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L99-L112

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

theorem PI.BeDiagZp.expT_add (x y : MvPowerSeries σ ℂ_[p]) (N : ℕ) :
    expT (x + y) N = ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range (N - m),
      (((m.factorial : ℂ_[p])⁻¹ * (j.factorial : ℂ_[p])⁻¹) • (x ^ m * y ^ j)) := by sorry
