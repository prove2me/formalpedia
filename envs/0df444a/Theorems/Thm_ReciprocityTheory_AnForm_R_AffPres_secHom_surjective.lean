-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_secHom_surjective
-- name    : ReciprocityTheory.AnForm.R.AffPres.secHom_surjective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:02.81425+00:00
-- url     : https://prove2.me/theorems/08b99bf5-a480-56ef-8925-f39c5c6501ff
-- title:
--   Aff Pres: sec Hom surjective
-- statement:
--   The Aff Pres construction uses the sec Hom surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SecHomSurjective.lean#L47-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/SecHomSurjective.lean#L47-L59

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

theorem ReciprocityTheory.AnForm.R.AffPres.secHom_surjective (P : AffPres sW) : Function.Surjective P.secHom := by sorry
