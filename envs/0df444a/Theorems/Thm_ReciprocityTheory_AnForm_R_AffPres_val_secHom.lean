-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_val_secHom
-- name    : ReciprocityTheory.AnForm.R.AffPres.val_secHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:37:55.938393+00:00
-- url     : https://prove2.me/theorems/4e071ea1-4437-5b88-b7bc-9e66593ba62e
-- title:
--   Aff Pres: val sec Hom
-- statement:
--   The Aff Pres construction uses the val sec Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SecHomSurjective.lean#L61-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SecHomSurjective.lean#L61-L90

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SecHomSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial
noncomputable section
variable {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}
open ReciprocityTheory.AnForm.R.AffPres

theorem ReciprocityTheory.AnForm.R.AffPres.val_secHom [LocallyOfFiniteType sW] (P : AffPres sW) (y : W) (hy : y ∈ P.V)
    (hc : IsClosed ({y} : Set W)) (f : MvPolynomial (Fin P.n) ℂ) :
    val sW (P.secHom f) y hy = eval (P.coord y hy) f := by sorry
