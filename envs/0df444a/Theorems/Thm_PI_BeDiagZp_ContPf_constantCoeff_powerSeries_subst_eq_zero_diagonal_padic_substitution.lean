-- Prove2me | Theorems.Thm_PI_BeDiagZp_ContPf_constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution
-- name    : PI.BeDiagZp.ContPf.constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:54.482152+00:00
-- url     : https://prove2.me/theorems/4566bebe-d4f2-437e-b320-118282d5f259
-- title:
--   Cont Pf: constant Coeff power Series subst eq zero diagonal padic substitution
-- statement:
--   The Cont Pf construction uses the constant Coeff power Series subst eq zero diagonal padic substitution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L77-L80

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

theorem PI.BeDiagZp.ContPf.constantCoeff_powerSeries_subst_eq_zero_diagonal_padic_substitution {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (F : PowerSeries ℂ_[p]) (hF : PowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a F) = 0 := by sorry
