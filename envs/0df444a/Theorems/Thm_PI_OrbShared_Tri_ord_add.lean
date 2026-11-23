-- Prove2me | Theorems.Thm_PI_OrbShared_Tri_ord_add
-- name    : PI.OrbShared.Tri.ord_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:53.932254+00:00
-- url     : https://prove2.me/theorems/143a44b8-b3cf-413f-9295-8ae83a384828
-- title:
--   Tri: ord add
-- statement:
--   The Tri construction uses the ord add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L32-L34

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

theorem PI.OrbShared.Tri.ord_add {f g : MvPowerSeries σ K} {n : ℕ} (hf : (n : ℕ∞) ≤ f.order) (hg : (n : ℕ∞) ≤ g.order) :
    (n : ℕ∞) ≤ (f + g).order := by sorry
