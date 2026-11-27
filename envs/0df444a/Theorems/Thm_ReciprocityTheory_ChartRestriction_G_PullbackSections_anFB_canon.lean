-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anFB_canon
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.anFB_canon
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:51:33.319818+00:00
-- url     : https://prove2.me/theorems/b4946cf5-f7f6-55d8-9b19-d120562a934d
-- title:
--   Pullback Sections: an FB canon
-- statement:
--   The Pullback Sections construction uses the an FB canon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ComposeLinearAction.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/ComposeLinearAction.lean#L112-L118

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.anFB_canon [StarRing (𝓞 E)] (ty : Fin g → (E →+* ℂ)) : (anFB ty).IsCanonGauge ℂ 0 := by sorry
