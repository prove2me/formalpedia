-- Prove2me | Theorems.Thm_PI_BeDiagZp_IntegralPowerSeriesBall_coeff_expMv
-- name    : PI.BeDiagZp.IntegralPowerSeriesBall.coeff_expMv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:31.615078+00:00
-- url     : https://prove2.me/theorems/4f542634-7a5d-4d3e-8d39-260c330f7f0c
-- title:
--   Integral Power Series Ball: coeff exp Mv
-- statement:
--   The Integral Power Series Ball construction uses the coeff exp Mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/CoeffPowMulPowEqZeroOfLt.lean#L48-L50

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

theorem PI.BeDiagZp.IntegralPowerSeriesBall.coeff_expMv (f : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1), coeff α (f ^ n) / (n.factorial : ℂ_[p]) := by sorry
