-- Prove2me | Theorems.Thm_PI_BeDiagZp_SubstW_coeff_expMv_eq
-- name    : PI.BeDiagZp.SubstW.coeff_expMv_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:59.556412+00:00
-- url     : https://prove2.me/theorems/11e4582f-69da-53ed-930f-26ce669bb5d0
-- title:
--   Subst W: coeff exp Mv eq
-- statement:
--   The Subst W construction uses the coeff exp Mv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L104-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L104-L117

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
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
open PI PI.BeDiagZp PI.BeDiagZp.SubstW
variable {p : ℕ} [Fact p.Prime]

theorem PI.BeDiagZp.SubstW.coeff_expMv_eq {σ : Type*} {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) (d : σ →₀ ℕ) {N : ℕ} (hN : d.degree < N) :
    MvPowerSeries.coeff d (expMv F) =
      ∑ n ∈ Finset.range N, MvPowerSeries.coeff d (F ^ n) / (n.factorial : ℂ_[p]) := by sorry
