-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P19_localization_adjunction
-- name    : QAlgorithms.Papers.Independent.Intake100.P19.localization_adjunction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:24:44.201123+00:00
-- url     : https://prove2.me/theorems/083ae946-4e94-4702-918b-b4177eefbf82
-- title:
--   Localization preserves adjunctions and full faithfulness
-- statement:
--   Let $F:\mathcal B\rightleftarrows\mathcal C:G$ be an adjoint pair. Let $S$ and $T$ be classes of morphisms in $\mathcal B$ and $\mathcal C$, with $F(S)\subseteq T$ and $G(T)\subseteq S$. The induced functors satisfy
--
--   $$\widetilde F:S^{-1}\mathcal B\rightleftarrows T^{-1}\mathcal C:\widetilde G,\qquad \widetilde F\dashv\widetilde G.$$
--
--   If $F$ is fully faithful, then $\widetilde F$ is fully faithful. No fractions or saturation assumptions are imposed. This transports the classifying-space adjunction to further localizations.
-- source:
--   Homotopy types of topological stacks, arXiv:0808.3799v2, PDF p. 14, Lemma 7.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P19

open CategoryTheory CategoryTheory.Limits

universe uB vB uC vC

/-- Lemma 7.5 (PDF p. 14): localizing an adjunction induces an adjunction;
its left functor remains fully faithful when the original left functor is.
No calculus-of-fractions or saturation hypothesis is imposed. -/
theorem localization_adjunction
    {B : Type uB} [Category.{vB} B] {C : Type uC} [Category.{vC} C]
    (F : B ⥤ C) (G : C ⥤ B) (adj : F ⊣ G)
    (S : MorphismProperty B) (T : MorphismProperty C)
    (hF : ∀ ⦃b b2 : B⦄ (f : b ⟶ b2), S f → T (F.map f))
    (hG : ∀ ⦃c c2 : C⦄ (g : c ⟶ c2), T g → S (G.map g)) :
    Nonempty (localizedFunctor F S T hF ⊣ localizedFunctor G T S hG) ∧
      ((F.Full ∧ F.Faithful) →
        (localizedFunctor F S T hF).Full ∧ (localizedFunctor F S T hF).Faithful) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P19

end
