-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_toW
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.app_toW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:35.232861+00:00
-- url     : https://prove2.me/theorems/0f8bb380-2ae9-4851-80e1-8090579736a9
-- title:
--   TG: app to W
-- statement:
--   The TG construction uses the app to W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L16-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenFlat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenThick
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
noncomputable section
variable {R : Type} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.app_toW {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (f : Y ⟶ X) (W : X.Opens) (r : R) :
    (f.app W).hom (toW p W r) = toW (f ≫ p) (f ⁻¹ᵁ W) r := by sorry
