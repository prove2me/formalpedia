-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_appTop_eq_of_gm
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.appTop_eq_of_gm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:24:47.604178+00:00
-- url     : https://prove2.me/theorems/0f904665-f957-544f-8f49-bf34281e07ce
-- title:
--   Tor: app Top eq of gm
-- statement:
--   The Tor construction uses the app Top eq of gm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GtPtsVal.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GtPtsVal.lean#L21-L31

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsTor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsVal
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {Y Z W : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.appTop_eq_of_gm (τ₁ τ₂ : Z ⟶ Y) (c₁ c₂ : Γ(Y, ⊤)ˣ) (h : ∀ z, gm τ₁ z ⊤ c₁ = gm τ₂ z ⊤ c₂) :
    τ₁.appTop.hom c₁.val = τ₂.appTop.hom c₂.val := by sorry
