-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_map_germ_ideal_eq_of_le
-- name    : ReciprocityTheory.AnForm.R.map_germ_ideal_eq_of_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:20.198509+00:00
-- url     : https://prove2.me/theorems/c01ac92a-9887-5bbd-8a16-6287f73a4af8
-- title:
--   R: map germ ideal eq of le
-- statement:
--   The R construction uses the map germ ideal eq of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L11-L19

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u

theorem ReciprocityTheory.AnForm.R.map_germ_ideal_eq_of_le {W : Scheme.{u}} (G : W.IdealSheafData) {U V : W.affineOpens} (h : U ≤ V)
    (x : W) (hx : x ∈ U.1) :
    Ideal.map (W.presheaf.germ V.1 x (h hx)).hom (G.ideal V) =
      Ideal.map (W.presheaf.germ U.1 x hx).hom (G.ideal U) := by sorry
