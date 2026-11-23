-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ds_stalkId_eq_map
-- name    : ReciprocityTheory.AnForm.R.ds_stalkId_eq_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:34.225802+00:00
-- url     : https://prove2.me/theorems/f54ab115-c2cc-4079-8040-42e60a5e6cf7
-- title:
--   R: ds stalk Id eq map
-- statement:
--   The R construction uses the ds stalk Id eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L21-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L21-L43

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

theorem ReciprocityTheory.AnForm.R.ds_stalkId_eq_map {W : Scheme.{u}} (G : W.IdealSheafData) (U : W.affineOpens) (x : W)
    (hx : x ∈ U.1) :
    FinalTheorems.stalkId G x = Ideal.map (W.presheaf.germ U.1 x hx).hom (G.ideal U) := by sorry
