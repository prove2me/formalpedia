-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_mono
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.PTAgree.mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:30.416553+00:00
-- url     : https://prove2.me/theorems/7858dece-6f24-586e-b54f-3ffa6a0c70db
-- title:
--   PTAgree: mono
-- statement:
--   The PTAgree construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtOrderProdSub.lean#L16-L17

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.PTAgree.mono {k l : ℕ} {A A' : ι → MvPowerSeries τ R} (h : PTAgree k A A') (hl : l ≤ k) :
    PTAgree l A A' := by sorry
