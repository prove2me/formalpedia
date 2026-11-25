-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_WMult_stalkId_eq_map_germ
-- name    : ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:59:12.05053+00:00
-- url     : https://prove2.me/theorems/df7e9806-a08e-5dd8-9e7c-57bc28c7d41e
-- title:
--   WMult: stalk Id eq map germ
-- statement:
--   The WMult construction uses the stalk Id eq map germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultA.lean#L10-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultA.lean#L10-L31

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.WMult
open AlgebraicGeometry CategoryTheory IsLocalRing
variable {W : Scheme.{0}}

theorem ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ (I : W.IdealSheafData) (y : W) (U : W.affineOpens) (hy : y ∈ U.1) :
    FinalTheorems.stalkId I y = Ideal.map (W.presheaf.germ U.1 y hy).hom (I.ideal U) := by sorry
