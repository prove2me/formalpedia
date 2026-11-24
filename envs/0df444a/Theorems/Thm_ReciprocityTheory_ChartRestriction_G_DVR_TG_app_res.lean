-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_app_res
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.app_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:01.376202+00:00
-- url     : https://prove2.me/theorems/34563ad4-e10d-41e9-b301-e4b54aa4b8a8
-- title:
--   TG: app res
-- statement:
--   The TG construction uses the app res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenThick.lean#L25-L29

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.app_res {X Y : Scheme.{0}} (f : Y ⟶ X) {V W : X.Opens} (h : W ≤ V) (x : Γ(X, V)) :
    (Y.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom x) =
      (f.app W).hom ((X.presheaf.map (homOfLE h).op).hom x) := by sorry
