-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_scal_unit_K
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.scal_unit_K
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:51:24.557544+00:00
-- url     : https://prove2.me/theorems/977c9f07-7bb8-4d72-9119-0230b2fb91da
-- title:
--   DVR: scal unit K
-- statement:
--   The DVR construction uses the scal unit K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L227-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L227-L244

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
variable {G : Over (Spec (CommRingCat.of V))}

theorem ReciprocityTheory.ChartRestriction.G.DVR.scal_unit_K (lam : V) (hlam : lam ≠ 0) {W : (pullback G.hom (jK V)).Opens} :
    IsUnit (resTop W (scal (pullback.snd G.hom (jK V) ≫ jK V) lam)) := by sorry
