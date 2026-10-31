-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P86_basedRingHom_preserves_bar
-- name    : QAlgorithms.Papers.Independent.Intake100.P86.basedRingHom_preserves_bar
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:27:48.840077+00:00
-- url     : https://prove2.me/theorems/c66e7bd2-8a3a-420c-bd98-a1e4b3c380bc
-- title:
--   Unital based homomorphisms preserve the hypergroup involution
-- statement:
--   Let $(A,B)$ and $(A',B')$ be hypergroups over $\mathbb Z$ in the sense of Definition 1.2.1: their distinguished bases contain the unit, have nonnegative integral structure constants, and satisfy the canonical involution and reciprocity axioms. Let $f:A\to A'$ be a unital homomorphism of based rings, so each element of $B$ maps to an element of $B'$ or to zero. Write $\overline{\phantom{a}}_A$ and $\overline{\phantom{a}}_{A'}$ for the respective canonical anti-involutions. Then
--
--   $$
--    f(\overline a_A)=\overline{f(a)}_{A'}\qquad(a\in A).
--   $$
--
--   Thus the canonical hypergroup involutions are compatible with every unital based homomorphism, without injectivity, surjectivity, or trace-preservation assumptions.
-- source:
--   Constructing cell data for diagram algebras, arXiv:math/0503751v3, PDF p. 10, Proposition 1.3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P86

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P86

/-- Proposition 1.3.3, PDF pp.10–11: a unital based homomorphism
intertwines the canonical hypergroup anti-involutions on every element. -/
theorem basedRingHom_preserves_bar
    {A I A2 I2 : Type*} [Ring A] [Ring A2]
    (H : IntegralHypergroup A I) (H2 : IntegralHypergroup A2 I2)
    (f : BasedRingHom H H2) :
    ∀ a : A, f.hom (H.bar a) = H2.bar (f.hom a) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P86

end
