-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_sncAt_of_not_mem
-- name    : ReciprocityTheory.AnForm.R.sncAt_of_not_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:07:19.284096+00:00
-- url     : https://prove2.me/theorems/eb25f0ab-eac8-44d3-8b91-53049eb9b6b0
-- title:
--   R: snc At of not mem
-- statement:
--   The R construction uses the snc At of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsC.lean#L9-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsC.lean#L9-L41

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsC
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

theorem ReciprocityTheory.AnForm.R.sncAt_of_not_mem {Y : Scheme.{0}} (B : TopologicalSpace.Closeds Y) (y : Y)
    (hy : y ∉ (B : Set Y)) (hreg : IsRegularLocalRing (Y.presheaf.stalk y)) :
    FinalTheorems.SncAt (Scheme.IdealSheafData.vanishingIdeal B) y := by sorry
