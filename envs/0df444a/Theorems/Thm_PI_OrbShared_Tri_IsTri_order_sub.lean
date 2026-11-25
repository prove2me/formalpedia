-- Prove2me | Theorems.Thm_PI_OrbShared_Tri_IsTri_order_sub
-- name    : PI.OrbShared.Tri.IsTri.order_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:16:41.31294+00:00
-- url     : https://prove2.me/theorems/cee1dab3-fa58-46e8-9ad1-4cbaaf7f66a1
-- title:
--   Is Tri: order sub
-- statement:
--   The Is Tri construction uses the order sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L92-L99

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

theorem PI.OrbShared.Tri.IsTri.order_sub (ha : IsTri c a) (v : σ) : ((2 : ℕ) : ℕ∞) ≤ (a v - C c * X v).order := by sorry
