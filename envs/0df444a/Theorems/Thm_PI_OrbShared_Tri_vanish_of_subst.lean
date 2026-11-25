-- Prove2me | Theorems.Thm_PI_OrbShared_Tri_vanish_of_subst
-- name    : PI.OrbShared.Tri.vanish_of_subst
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:35:35.625119+00:00
-- url     : https://prove2.me/theorems/8ba9941b-1a41-4337-a1d7-5d12c1f600ec
-- title:
--   Tri: vanish of subst
-- statement:
--   The Tri construction uses the vanish of subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L147-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L147-L165

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
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
open PI PI.OrbShared PI.OrbShared.Tri
open MvPowerSeries Finsupp
variable {K : Type*} [Field K] {σ : Type*} [Finite σ]
variable {c : K} {a : σ → MvPowerSeries σ K}

theorem PI.OrbShared.Tri.vanish_of_subst (hc : c ≠ 0) (ha : IsTri c a) (F : MvPowerSeries σ K) (n : ℕ)
    (h : ∀ m : σ →₀ ℕ, m.degree < n → coeff m (subst a F) = 0) :
    ∀ m : σ →₀ ℕ, m.degree < n → coeff m F = 0 := by sorry
