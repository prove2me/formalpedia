-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P19_fullSubcategory_adjunction
-- name    : QAlgorithms.Papers.Independent.Intake100.P19.fullSubcategory_adjunction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:24:13.489845+00:00
-- url     : https://prove2.me/theorems/b0d09b2c-b383-4656-955c-381b33e744cc
-- title:
--   Restriction of an adjunction to full subcategories
-- statement:
--   Let $F:\mathcal B\rightleftarrows\mathcal C:G$ be an adjoint pair. Let $\mathcal B'\subseteq\mathcal B$ and $\mathcal C'\subseteq\mathcal C$ be full subcategories with $F(\mathcal B')\subseteq\mathcal C'$ and $G(\mathcal C')\subseteq\mathcal B'$. The actual restrictions satisfy
--
--   $$F|_{\mathcal B'}\dashv G|_{\mathcal C'}.$$
--
--   This permits restricting the classifying-space adjunction to prescribed classes of objects. Empty full subcategories are permitted.
-- source:
--   Homotopy types of topological stacks, arXiv:0808.3799v2, PDF p. 14, Lemma 7.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P19

open CategoryTheory CategoryTheory.Limits

universe uB vB uC vC

/-- Lemma 7.4 (PDF p. 14): an adjunction restricts to full subcategories
preserved by its two functors. There are no nonemptiness assumptions. -/
theorem fullSubcategory_adjunction
    {B : Type uB} [Category.{vB} B] {C : Type uC} [Category.{vC} C]
    (F : B ⥤ C) (G : C ⥤ B) (adj : F ⊣ G)
    (P : ObjectProperty B) (Q : ObjectProperty C)
    (hF : ∀ b, P b → Q (F.obj b)) (hG : ∀ c, Q c → P (G.obj c)) :
    Nonempty (restrictedFunctor F P Q hF ⊣ restrictedFunctor G Q P hG) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P19

end
