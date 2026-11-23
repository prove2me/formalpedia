-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_res
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.toW_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:22.098528+00:00
-- url     : https://prove2.me/theorems/840d2967-f810-463e-9b3e-b4428d31ce0d
-- title:
--   TG: to W res
-- statement:
--   The TG construction uses the to W res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L11-L14

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.toW_res {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) {V W : X.Opens} (h : W ≤ V) (r : R) :
    (X.presheaf.map (homOfLE h).op).hom (toW p V r) = toW p W r := by sorry
