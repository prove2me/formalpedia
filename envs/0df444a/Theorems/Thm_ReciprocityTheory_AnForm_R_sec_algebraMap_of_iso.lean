-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_sec_algebraMap_of_iso
-- name    : ReciprocityTheory.AnForm.R.sec_algebraMap_of_iso
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:01:18.207484+00:00
-- url     : https://prove2.me/theorems/cde6fc60-fc2b-4dcc-bbb7-6cf93efa257d
-- title:
--   R: sec algebra Map of iso
-- statement:
--   The R construction uses the sec algebra Map of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsA.lean#L33-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsA.lean#L33-L67

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjBCompl
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
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

theorem ReciprocityTheory.AnForm.R.sec_algebraMap_of_iso {X W : Scheme.{0}} (π : W ⟶ X) (U : X.affineOpens) (V : W.Opens)
    (hV : V ≤ π ⁻¹ᵁ U.1) (A : Type) [CommRing A] [Algebra Γ(X, U.1) A]
    (e : V.toScheme ≅ Spec (.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) A)) ≫ U.2.fromSpec = V.ι ≫ π)
    (r : Γ(X, U.1)) :
    V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (algebraMap _ A r))) = π.appLE _ V hV r := by sorry
