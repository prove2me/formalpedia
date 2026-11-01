-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P71_braidedButterfly_transfer
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P71.braidedButterfly_transfer
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:42:06.797749+00:00
-- url     : https://prove2.me/theorems/826229bc-f580-43d1-993e-b7ae596feccb
-- title:
--   Lemma 7.4.6: transfer of symmetry and Picardness
-- statement:
--   Let $[H_\bullet,E,G_\bullet]$ be a braided butterfly on a subcanonical site $S$, with specified right-action brackets $c_H$ and $c_G$. A bracket is symmetric when $c(x,y)=c(y,x)^{-1}$, and Picard when it is symmetric and $c(x,x)=1$, for all local sections.
--
--   1. If $j:E\to G_0$ is locally epimorphic, symmetry of $c_H$ implies symmetry of $c_G$, and Picardness of $c_H$ implies Picardness of $c_G$.
--   2. If $\kappa:H_1\to E$ is a monomorphism, the reverse implications hold.
--
--   Consequently, for a reversible braided butterfly,
--
--   $$
--   H_\bullet\text{ is symmetric}\iff G_\bullet\text{ is symmetric},\qquad
--   H_\bullet\text{ is Picard}\iff G_\bullet\text{ is Picard}.
--   $$
--
--   These statements allow commutativity constraints to pass along suitable weak morphisms and equivalences. The monomorphism condition in the second part is the explicit condition used by the source cancellation argument.
-- source:
--   Butterflies I: morphisms of 2-group stacks, arXiv:0808.3627v2, PDF p. 72, Lemma 7.4.6: transfer of symmetry and Picardness

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P71

namespace QAlgorithms.Papers.Independent.Intakenext100.P71

open CategoryTheory Opposite

universe u v w

variable {C : Type u} [Category.{v} C]

variable {J : GrothendieckTopology C}

/-- Lemma 7.4.6 and its following reversible consequence,
arXiv:0808.3627v2, PDF p.72.
Correction: the second premise is the explicit monicity of kappa used by
the cancellation argument; the printed equivalence with triviality of the
entire homotopy kernel is false. Both symmetry and Picardness are retained. -/
theorem braidedButterfly_transfer [J.Subcanonical]
    {H G : RightCrossedModule.{u, v, w} J}
    (E : Butterfly H G) (cH : Braiding H) (cG : Braiding G)
    (hbraided : E.IsBraided cH cG) :
    (IsLocalEpi E.j →
      (cH.IsSymmetric → cG.IsSymmetric) ∧ (cH.IsPicard → cG.IsPicard)) ∧
    ((∀ U, Function.Injective (onSections E.kappa U)) →
      (cG.IsSymmetric → cH.IsSymmetric) ∧ (cG.IsPicard → cH.IsPicard)) ∧
    (E.IsReversible →
      (cH.IsSymmetric ↔ cG.IsSymmetric) ∧ (cH.IsPicard ↔ cG.IsPicard)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P71
