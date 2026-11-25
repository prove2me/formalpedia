-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_order_prod_sub
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.pt_order_prod_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:36:00.639855+00:00
-- url     : https://prove2.me/theorems/bd4fcc23-eedd-4dac-b613-ba97636b3e83
-- title:
--   Sh: pt order prod sub
-- statement:
--   The Sh construction uses the pt order prod sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L106-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L106-L124

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.pt_order_prod_sub {σ : Type*} {A A' : σ → MvPowerSeries τ R} {j : ℕ}
    (hA : ∀ s, constantCoeff (A s) = 0) (hA' : ∀ s, constantCoeff (A' s) = 0)
    (hAA : ∀ s, ((j + 1 : ℕ) : ℕ∞) ≤ (A s - A' s).order) (α : σ →₀ ℕ) (S : Finset σ) :
    ((j + ∑ s ∈ S, α s : ℕ) : ℕ∞) ≤
      (∏ s ∈ S, A s ^ α s - ∏ s ∈ S, A' s ^ α s).order := by sorry
