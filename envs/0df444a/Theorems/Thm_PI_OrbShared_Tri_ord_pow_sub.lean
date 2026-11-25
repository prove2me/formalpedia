-- Prove2me | Theorems.Thm_PI_OrbShared_Tri_ord_pow_sub
-- name    : PI.OrbShared.Tri.ord_pow_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:16:32.511539+00:00
-- url     : https://prove2.me/theorems/40c5bd48-c25a-4bec-890d-d5d86d931187
-- title:
--   Tri: ord pow sub
-- statement:
--   The Tri construction uses the ord pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L41-L51

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

theorem PI.OrbShared.Tri.ord_pow_sub {x y : MvPowerSeries σ K} (hx : 1 ≤ x.order) (hy : 1 ≤ y.order)
    (hxy : ((2 : ℕ) : ℕ∞) ≤ (y - x).order) (n : ℕ) : ((n + 1 : ℕ) : ℕ∞) ≤ (y ^ n - x ^ n).order := by sorry
