-- Prove2me | Theorems.Thm_PI_OrbShared_Tri_coeff_P_of_le
-- name    : PI.OrbShared.Tri.coeff_P_of_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:16:29.936336+00:00
-- url     : https://prove2.me/theorems/1c02c696-ddb3-5f27-9a84-941281c5468e
-- title:
--   Tri: coeff P of le
-- statement:
--   The Tri construction uses the coeff P of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L101-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L101-L113

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

theorem PI.OrbShared.Tri.coeff_P_of_le (ha : IsTri c a) (d e : σ →₀ ℕ) (he : e.degree ≤ d.degree) :
    coeff e (P a d) = if e = d then c ^ d.degree else 0 := by sorry
