-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P19_spans_present_localization
-- name    : QAlgorithms.Papers.Independent.Intake100.P19.spans_present_localization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:25:22.188037+00:00
-- url     : https://prove2.me/theorems/7b906c99-606d-475e-8e26-85be912d0c15
-- title:
--   Spans modulo zigzags present the localization
-- statement:
--   Let $\mathcal C$ be a category and $R$ a class containing identities and closed under composition and base change. Assume pullbacks along morphisms in $R$ exist. The category $\operatorname{Span}_R(X,Y)$ has spans $X\xleftarrow r V\xrightarrow g Y$ with $r\in R$ as objects and all commuting maps of apices as morphisms. For the actual localization functor $Q$, there are canonical simultaneous bijections
--
--   $$\pi_0\operatorname{Span}_R(X,Y)\cong\operatorname{Hom}_{R^{-1}\mathcal C}(QX,QY),\qquad [(r,g)]\longmapsto Q(r)^{-1}Q(g).$$
--
--   Components use arbitrary finite zigzags of maps of spans. Composition is induced by pullback composition, and each honest arrow $f$ is represented by $(\mathrm{id},f)$. This presents the localization with its universal property. No Gabriel–Zisman cancellation axiom is assumed.
-- source:
--   Homotopy types of topological stacks, arXiv:0808.3799v2, PDF p. 28, §13, unnumbered: spans realize localization

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P19

open CategoryTheory CategoryTheory.Limits

universe uB vB uC vC

/-- Appendix I, unnumbered localization assertion (PDF pp. 28–29): the
component sets of spans give precisely the localization, with honest arrows
(id,f) and composition by pullback. The simultaneous Hom equivalences below,
including their composition and identity formulas, specify this presentation.
No Gabriel–Zisman cancellation axiom is assumed. -/
theorem spans_present_localization
    {C : Type uC} [Category.{vC} C] (R : MorphismProperty C)
    [R.ContainsIdentities] [R.IsStableUnderComposition]
    [R.IsStableUnderBaseChange] [R.HasPullbacks] :
    R.Q.IsLocalization R ∧
      ∃ e : ∀ X Y : C, SpanComponent R X Y ≃ (R.Q.obj X ⟶ R.Q.obj Y),
        (∀ (X Y : C) (s : RightSpan R X Y),
          e X Y (Quot.mk _ s) = spanValue R s) ∧
        (∀ (X Y Z : C) (s : RightSpan R X Y) (t : RightSpan R Y Z),
          e X Z (Quot.mk _ (composeSpan R s t)) =
            e X Y (Quot.mk _ s) ≫ e Y Z (Quot.mk _ t)) ∧
        (∀ (X Y : C) (f : X ⟶ Y),
          e X Y (Quot.mk _ (honestSpan R f)) = R.Q.map f) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P19

end
