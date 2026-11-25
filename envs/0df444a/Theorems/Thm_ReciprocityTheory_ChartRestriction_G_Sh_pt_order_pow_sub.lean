-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_order_pow_sub
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.pt_order_pow_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:35:33.400472+00:00
-- url     : https://prove2.me/theorems/b13ab6ae-b018-4e3e-be07-624bbc00b7e1
-- title:
--   Sh: pt order pow sub
-- statement:
--   The Sh construction uses the pt order pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L83-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L83-L94

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.pt_order_pow_sub {f g : MvPowerSeries τ R} {j : ℕ}
    (hfg : ((j + 1 : ℕ) : ℕ∞) ≤ (f - g).order) (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) (m : ℕ) : ((j + m : ℕ) : ℕ∞) ≤ (f ^ m - g ^ m).order := by sorry
