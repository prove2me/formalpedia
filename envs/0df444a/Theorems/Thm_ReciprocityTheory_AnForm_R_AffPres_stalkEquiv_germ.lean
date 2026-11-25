-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_stalkEquiv_germ
-- name    : ReciprocityTheory.AnForm.R.AffPres.stalkEquiv_germ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:31:44.881839+00:00
-- url     : https://prove2.me/theorems/c14796f7-14cf-5ffc-b9dd-99fdb4519484
-- title:
--   Aff Pres: stalk Equiv germ
-- statement:
--   The Aff Pres construction uses the stalk Equiv germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLoc.lean#L191-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLoc.lean#L191-L193

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

theorem ReciprocityTheory.AnForm.R.AffPres.stalkEquiv_germ (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) (f : MvPolynomial (Fin P.n) ℂ) :
    P.stalkEquiv x hx hc (W.presheaf.germ P.V x hx (P.secHom f)) =
      algebraMap _ (locRing P.K (P.coord x hx)) f := by sorry
