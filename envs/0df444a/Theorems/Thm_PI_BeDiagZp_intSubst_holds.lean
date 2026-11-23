-- Prove2me | Theorems.Thm_PI_BeDiagZp_intSubst_holds
-- name    : PI.BeDiagZp.intSubst_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:45.040121+00:00
-- url     : https://prove2.me/theorems/3f41de18-b364-4545-987c-e147a511d9ad
-- title:
--   Be Diag Zp: int Subst holds
-- statement:
--   The Be Diag Zp construction uses the int Subst holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L81-L86

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
open PI PI.BeDiagZp
open SubstW

theorem PI.BeDiagZp.intSubst_holds : ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (f : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (s i) = 0) →
    (∀ i, IntegralMv (s i)) → IntegralMv f → IntegralMv (MvPowerSeries.subst s f) := by sorry
