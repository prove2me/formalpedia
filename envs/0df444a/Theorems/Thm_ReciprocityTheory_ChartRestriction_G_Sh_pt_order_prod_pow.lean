-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_order_prod_pow
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.pt_order_prod_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:57.358546+00:00
-- url     : https://prove2.me/theorems/bdd08249-f392-48df-a245-b9c07c9e1431
-- title:
--   Sh: pt order prod pow
-- statement:
--   The Sh construction uses the pt order prod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L96-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L96-L104

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.pt_order_prod_pow {σ : Type*} (A : σ → MvPowerSeries τ R)
    (hA : ∀ s, constantCoeff (A s) = 0) (α : σ →₀ ℕ) (S : Finset σ) :
    ((∑ s ∈ S, α s : ℕ) : ℕ∞) ≤ (∏ s ∈ S, A s ^ α s).order := by sorry
