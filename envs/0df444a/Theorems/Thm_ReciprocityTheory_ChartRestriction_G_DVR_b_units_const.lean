-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_b_units_const
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.b_units_const
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:17.741857+00:00
-- url     : https://prove2.me/theorems/5c9c4a42-a438-456f-b568-17d79b8131cb
-- title:
--   DVR: b units const
-- statement:
--   The DVR construction uses the b units const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L74-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem ReciprocityTheory.ChartRestriction.G.DVR.b_units_const (hGF : GlobalFnsSt) (D : DegData V (maximalIdeal V)) (f : Γ(D.toPre.P.A.left, ⊤)ˣ) :
    ∃ c : Γ(Spec (CommRingCat.of V), ⊤)ˣ, f = Units.map (D.toPre.P.A.hom.appTop).hom.toMonoidHom c := by sorry
