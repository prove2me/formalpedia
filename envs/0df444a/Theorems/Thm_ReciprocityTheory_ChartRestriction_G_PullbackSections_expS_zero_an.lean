-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_expS_zero_an
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.expS_zero_an
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:51:50.545518+00:00
-- url     : https://prove2.me/theorems/0c7f1701-b60f-5ba2-8a0a-e12044048595
-- title:
--   Pullback Sections: exp S zero an
-- statement:
--   The Pullback Sections construction uses the exp S zero an property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ComposeLinearAction.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ComposeLinearAction.lean#L35-L41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_ComposeLinearAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ NumberField
variable {g m n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.expS_zero_an (k : Type) [CommRing k] [Algebra ℚ k] {n d : ℕ} : FB.expS k (0 : PS k n d) = 1 := by sorry
