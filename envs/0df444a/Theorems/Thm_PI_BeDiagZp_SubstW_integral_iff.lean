-- Prove2me | Theorems.Thm_PI_BeDiagZp_SubstW_integral_iff
-- name    : PI.BeDiagZp.SubstW.integral_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:58.924679+00:00
-- url     : https://prove2.me/theorems/696d7f69-8e6a-4a93-99ad-d226b99d2163
-- title:
--   Subst W: integral iff
-- statement:
--   The Subst W construction uses the integral iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DiagonalPadicSubstitution/PowerSeriesDiagonalLinear.lean#L70-L73

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

theorem PI.BeDiagZp.SubstW.integral_iff {p : ℕ} [Fact p.Prime] {σ : Type*} (f : MvPowerSeries σ ℂ_[p]) :
    IntegralMv f ↔ f ∈ SerS (Rint p) σ := by sorry
