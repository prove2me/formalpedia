-- Prove2me | Theorems.Thm_PI_BeDiagZp_SubstW_expMv_subst
-- name    : PI.BeDiagZp.SubstW.expMv_subst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:14.724032+00:00
-- url     : https://prove2.me/theorems/5f23943f-a315-573e-be1d-9829181d2877
-- title:
--   Subst W: exp Mv subst
-- statement:
--   The Subst W construction uses the exp Mv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L129-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L129-L160

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

theorem PI.BeDiagZp.SubstW.expMv_subst {σ τ : Type*} [Finite σ] {s : σ → MvPowerSeries τ ℂ_[p]}
    (hs0 : ∀ i, MvPowerSeries.constantCoeff (s i) = 0) {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    expMv (MvPowerSeries.subst s F) = MvPowerSeries.subst s (expMv F) := by sorry
