-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P59_ordinaryEquivalence_iff_quasiInverse
-- name    : QAlgorithms.Papers.Independent.Intake100.P59.ordinaryEquivalence_iff_quasiInverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:03:24.826421+00:00
-- url     : https://prove2.me/theorems/3d7f0acd-a7fe-4c3e-a724-7617f0f95f3d
-- title:
--   Equivalence of categories and quasi-inverses
-- statement:
--   Let $A$ and $B$ be ordinary categories in compatible fixed universes and let $F:A\to B$ be a functor. Then $F$ is full, faithful and essentially surjective if and only if there exists a functor $G:B\to A$ with natural isomorphisms
--
--   $$
--   G\circ F\cong\mathrm{id}_A,\qquad F\circ G\cong\mathrm{id}_B.
--   $$
--
--   This characterizes ordinary equivalences of categories. No smoothness is asserted.
--
--   **Formalization Note** The printed identity subscripts are reversed; the displayed formula uses the only type-correct identities. Independent moderation of this correction is pending.
-- source:
--   Orbifolds as stacks?, arXiv:0806.4160v2, PDF p. 8, Theorem 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P59

namespace QAlgorithms.Papers.Independent.Intake100.P59

open CategoryTheory

universe u v uC vC uD vD uE vE

/-- Theorem 3.3, PDF p.8: full faithfulness and essential surjectivity characterize
an ordinary categorical equivalence. The printed subscripts on the two identity
functors are reversed. Here `F ⋙ G` is compared with `𝟭 A`, and `G ⋙ F` with `𝟭 B`;
these are the only typed choices. This source correction requires independent moderation. -/
theorem ordinaryEquivalence_iff_quasiInverse
    {A : Type uC} {B : Type uD} [Category.{vC} A] [Category.{vD} B]
    (F : A ⥤ B) :
    (F.Full ∧ F.Faithful ∧ F.EssSurj) ↔
      ∃ G : B ⥤ A, Nonempty (F ⋙ G ≅ 𝟭 A) ∧ Nonempty (G ⋙ F ≅ 𝟭 B) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P59
