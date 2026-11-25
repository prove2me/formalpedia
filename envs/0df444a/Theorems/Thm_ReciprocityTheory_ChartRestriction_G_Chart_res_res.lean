-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_res_res
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.res_res
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:08:37.156623+00:00
-- url     : https://prove2.me/theorems/a6b65eb7-d482-4708-9205-55d14c424a06
-- title:
--   Chart: res res
-- statement:
--   The Chart construction uses the res res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L108-L111

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S]
variable {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem ReciprocityTheory.ChartRestriction.G.Chart.res_res {A A' A'' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] [CommRing A'']
    [Algebra S A''] (j : A →ₐ[S] A') (j' : A' →ₐ[S] A'') (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (dualMapS j') ≫ spMap (dualMapS j) ≫ y = spMap (dualMapS (j'.comp j)) ≫ y := by sorry
