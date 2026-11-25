-- Prove2me | Theorems.Thm_PI_BeDiagZp_ContPf_coeff_subst_eq_sum
-- name    : PI.BeDiagZp.ContPf.coeff_subst_eq_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:47.707288+00:00
-- url     : https://prove2.me/theorems/78e470d8-8302-452f-91ae-067b93dc9dd0
-- title:
--   Cont Pf: coeff subst eq sum
-- statement:
--   The Cont Pf construction uses the coeff subst eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/ConstantCoeffSubstEqZero.lean#L49-L59

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

theorem PI.BeDiagZp.ContPf.coeff_subst_eq_sum {σ : Type} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (F : PowerSeries ℂ_[p]) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (PowerSeries.subst a F) =
      ∑ d ∈ Finset.range (e.degree + 1), PowerSeries.coeff d F • MvPowerSeries.coeff e (a ^ d) := by sorry
