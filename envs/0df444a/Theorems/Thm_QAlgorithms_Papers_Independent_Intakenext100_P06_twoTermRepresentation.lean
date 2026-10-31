-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_twoTermRepresentation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.twoTermRepresentation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:48:25.633868+00:00
-- url     : https://prove2.me/theorems/9571e86e-49ea-449f-b7f6-5905410cfff0
-- title:
--   Two-term representation of a restrained Pic-category
-- statement:
--   Let $\mathcal C$ be a restrained Pic-category, meaning a symmetric monoidal Gr-category with identity self-symmetries. There are abelian groups $A,B$ and a homomorphism $d:B\to A$, viewed as a complex in degrees $1\to0$, for which
--
--   $$
--   \mathcal C\simeq_{\otimes,\mathrm{sym}}\mathcal G_d.
--   $$
--
--   Here $\mathcal G_d$ has actual objects $x\in A$, arrows $b:x\to y$ with $d(b)=y-x$, identity label $0$, and composition $b'\circ b=b'+b$. Tensor is addition on objects and arrow labels, the unit is $0$, and the associator, unitors, and symmetry have zero labels. The assertion includes the full monoidal and symmetric structures and their coherence, invertibility, restraint, and a symmetry-preserving strong monoidal equivalence.
--
--   This realizes the category by a concrete two-term complex without an extra exactness hypothesis.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 20, Appendix A, Theorem 17: two-term complex representation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Theorem 17, PDF p. 20, with the construction of PDF p. 13:
every restrained Pic-category has a two-term abelian-group model,
with all the specified tensor/coherence data and symmetry-preserving
strong monoidal equivalence. -/
theorem twoTermRepresentation {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [SymmetricCategory C]
    (h : IsWeakTwoGroup C) (r : Restrained C) :
    ∃ (A : Type (max u v)) (a : AddCommGroup A)
      (B : Type (max u v)) (b : AddCommGroup B),
      letI := a
      letI := b
      ∃ (d : B →+ A) (m : MonoidalCategory (ChainCategory d)),
        letI := m
        ∃ s : SymmetricCategory (ChainCategory d),
          letI := s
          ChainTensorData d m ∧
          (∀ x y : ChainCategory d, (β_ x y).hom.val = 0) ∧
          IsWeakTwoGroup (ChainCategory d) ∧ Restrained (ChainCategory d) ∧
          Nonempty (PicEquivalence C (ChainCategory d)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
