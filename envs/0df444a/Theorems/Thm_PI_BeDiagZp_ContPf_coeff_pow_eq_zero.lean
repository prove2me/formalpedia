-- Prove2me | Theorems.Thm_PI_BeDiagZp_ContPf_coeff_pow_eq_zero
-- name    : PI.BeDiagZp.ContPf.coeff_pow_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:46.250345+00:00
-- url     : https://prove2.me/theorems/72176748-930c-585e-91d1-18d56e5465cc
-- title:
--   Cont Pf: coeff pow eq zero
-- statement:
--   The Cont Pf construction uses the coeff pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L44-L47

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
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
open PI PI.BeDiagZp PI.BeDiagZp.ContPf
variable {p : ℕ} [Fact p.Prime]

theorem PI.BeDiagZp.ContPf.coeff_pow_eq_zero {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (e : σ →₀ ℕ) (d : ℕ) (h : e.degree < d) : MvPowerSeries.coeff e (a ^ d) = 0 := by sorry
