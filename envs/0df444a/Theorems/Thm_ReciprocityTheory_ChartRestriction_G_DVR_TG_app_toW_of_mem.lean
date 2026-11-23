-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_toW_of_mem
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.app_toW_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:37.921292+00:00
-- url     : https://prove2.me/theorems/4f78e8e4-d2ca-4bcc-b075-da70bc3c4d49
-- title:
--   TG: app to W of mem
-- statement:
--   The TG construction uses the app to W of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L84-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L84-L108

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.app_toW_of_mem {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (W : X.Opens)
    {r : R} (hr : r ∈ J) : (pullback.fst p (tq J)).app W (toW p W r) = 0 := by sorry
