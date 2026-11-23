-- Prove2me | Theorems.Thm_PI_OrbShared_Tri_coeff_subst_tri
-- name    : PI.OrbShared.Tri.coeff_subst_tri
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:41.05919+00:00
-- url     : https://prove2.me/theorems/05cb2867-d38c-469b-af45-41420ef1d30f
-- title:
--   Tri: coeff subst tri
-- statement:
--   The Tri construction uses the coeff subst tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L115-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L115-L145

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

theorem PI.OrbShared.Tri.coeff_subst_tri (ha : IsTri c a) (F : MvPowerSeries σ K) (e : σ →₀ ℕ) :
    coeff e (subst a F) = c ^ e.degree * coeff e F +
      ∑ᶠ d, if d.degree < e.degree then coeff d F * coeff e (P a d) else 0 := by sorry
