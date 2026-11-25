-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_map_maximalIdeal_stalk
-- name    : ReciprocityTheory.AnForm.R.AffPres.map_maximalIdeal_stalk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:32:43.328353+00:00
-- url     : https://prove2.me/theorems/15ad73ce-768a-4df7-ba38-7831ea962851
-- title:
--   Aff Pres: map maximal Ideal stalk
-- statement:
--   The Aff Pres construction uses the map maximal Ideal stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLoc.lean#L213-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLoc.lean#L213-L224

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
open ReciprocityTheory.AnForm.R.AffPres
variable (P : AffPres s)

theorem ReciprocityTheory.AnForm.R.AffPres.map_maximalIdeal_stalk (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    (IsLocalRing.maximalIdeal (W.presheaf.stalk x)).map (P.stalkEquiv x hx hc) =
      Ideal.map (algebraMap _ (locRing P.K (P.coord x hx))) (ptIdeal (P.coord x hx)) := by sorry
