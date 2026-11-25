-- Prove2me | Theorems.Thm_PI_OrbShared_Tri_ord_prod_sub
-- name    : PI.OrbShared.Tri.ord_prod_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:16:36.808941+00:00
-- url     : https://prove2.me/theorems/0d629ea5-b844-5402-9de0-60dc75b19166
-- title:
--   Tri: ord prod sub
-- statement:
--   The Tri construction uses the ord prod sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L53-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean#L53-L71

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

theorem PI.OrbShared.Tri.ord_prod_sub {ι : Type*} (S : Finset ι) (x y : ι → MvPowerSeries σ K) (d : ι → ℕ)
    (hx : ∀ i, 1 ≤ (x i).order) (hy : ∀ i, 1 ≤ (y i).order)
    (hxy : ∀ i, ((2 : ℕ) : ℕ∞) ≤ (y i - x i).order) :
    ((∑ i ∈ S, d i : ℕ) : ℕ∞) ≤ (∏ i ∈ S, x i ^ d i).order ∧
      ((∑ i ∈ S, d i + 1 : ℕ) : ℕ∞) ≤ (∏ i ∈ S, y i ^ d i - ∏ i ∈ S, x i ^ d i).order := by sorry
