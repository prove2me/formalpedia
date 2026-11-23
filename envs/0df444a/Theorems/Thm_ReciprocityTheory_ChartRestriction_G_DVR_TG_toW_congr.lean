-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_toW_congr
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.toW_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:58.921608+00:00
-- url     : https://prove2.me/theorems/b89699f5-eb80-44fa-a71a-d9c0b951761c
-- title:
--   TG: to W congr
-- statement:
--   The TG construction uses the to W congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L22-L23

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.toW_congr {X : Scheme.{0}} {p p' : X ⟶ Spec (CommRingCat.of R)} (h : p = p') (W : X.Opens) (r : R) :
    toW p W r = toW p' W r := by sorry
