-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_subst_agree
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.pt_subst_agree
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:13.625251+00:00
-- url     : https://prove2.me/theorems/b8357cea-462d-4a54-aaee-ead2c4664add
-- title:
--   Sh: pt subst agree
-- statement:
--   The Sh construction uses the pt subst agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L126-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L126-L159

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries
noncomputable section
variable {R : Type*} [CommRing R] {τ : Type*} {ι : Type*}

theorem ReciprocityTheory.ChartRestriction.G.Sh.pt_subst_agree {σ : Type*} {A A' : σ → MvPowerSeries τ R} (hA : HasSubst A)
    (hA' : HasSubst A') (hA0 : ∀ s, constantCoeff (A s) = 0)
    (hA0' : ∀ s, constantCoeff (A' s) = 0) (K : MvPowerSeries σ R) (k : ℕ)
    (hAA : ∀ s (e : τ →₀ ℕ), e.degree < k → coeff e (A s) = coeff e (A' s))
    (hK : ∀ α, coeff α K ≠ 0 → 2 ≤ α.degree ∨ ∀ s ∈ α.support, A s = A' s) :
    ∀ e : τ →₀ ℕ, e.degree < k + 1 → coeff e (subst A K) = coeff e (subst A' K) := by sorry
