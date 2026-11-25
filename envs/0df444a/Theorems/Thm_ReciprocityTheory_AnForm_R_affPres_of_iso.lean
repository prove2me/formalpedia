-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_affPres_of_iso
-- name    : ReciprocityTheory.AnForm.R.affPres_of_iso
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:42:52.860257+00:00
-- url     : https://prove2.me/theorems/cfd7e429-4bd0-408b-bf8a-9401065cbe23
-- title:
--   R: aff Pres of iso
-- statement:
--   The R construction uses the aff Pres of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WCharts.lean#L12-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WCharts.lean#L12-L44

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section

theorem ReciprocityTheory.AnForm.R.affPres_of_iso {W : Scheme.{0}} (s : W ⟶ Spec (.of ℂ)) (V : W.Opens) (A : Type) [CommRing A]
    [Algebra ℂ A] (e : V.toScheme ≅ Spec (.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) = V.ι ≫ s) (n : ℕ) (y : Fin n → A)
    (hy : Algebra.adjoin ℂ (Set.range y) = ⊤) :
    ∃ (I : Ideal (MvPolynomial (Fin n) ℂ)) (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ I)))
      (hiso : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I))) = V.ι ≫ s),
      ∀ l : Fin n, (AffPres.mk V n I iso hiso : AffPres s).secHom (X l) =
        V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (y l))) := by sorry
