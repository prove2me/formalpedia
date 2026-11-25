-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_appLE_top_eq
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.appLE_top_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:17:21.514873+00:00
-- url     : https://prove2.me/theorems/ec167454-7406-50ce-966b-7b9854259a78
-- title:
--   DVR: app LE top eq
-- statement:
--   The DVR construction uses the app LE top eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThickKer.lean#L22-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThickKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [CommRing V] {X : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.DVR.appLE_top_eq {Y W : Scheme.{0}} (f : Y ⟶ W) (e : ⊤ ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ e = f.appTop := by sorry
