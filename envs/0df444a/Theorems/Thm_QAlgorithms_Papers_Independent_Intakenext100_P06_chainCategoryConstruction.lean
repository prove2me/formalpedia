-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_chainCategoryConstruction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.chainCategoryConstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:54:00.241294+00:00
-- url     : https://prove2.me/theorems/42285a05-6e9d-4c33-aad6-3b0ba2484856
-- title:
--   The concrete Pic-category of a two-term complex
-- statement:
--   Let $A,B$ be arbitrary abelian groups and $d:B\to A$ a homomorphism in degrees $1\to0$. Define the category $\mathcal G_d$ by
--
--   $$
--   \operatorname{Ob}(\mathcal G_d)=A,\qquad
--   \operatorname{Hom}(x,y)=\{b\in B:d(b)=y-x\},\qquad
--   b'\circ b=b'+b.
--   $$
--
--   The identity arrow has label $0$. Addition on objects and arrow labels gives a full monoidal structure with unit $0$ and zero-labelled associator and unitors. It extends to a symmetric monoidal structure whose symmetry has label $0$; all arrows are invertible, $-x$ is a two-sided weak inverse of $x$, and every self-symmetry is the identity. Thus $\mathcal G_d$ is a restrained Pic-category.
--
--   No square-zero or exactness assumption is needed for a single differential. This fixes the complete concrete model used in Theorem 17.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 13, §5: the concrete restrained Pic-category of a two-term complex

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Section 5, PDF p. 13: addition supplies the complete concrete
restrained Pic-category, including identity symmetry and weak inverse -x. -/
theorem chainCategoryConstruction {A : Type u} {B : Type v}
    [AddCommGroup A] [AddCommGroup B] (d : B →+ A) :
    ∃ m : MonoidalCategory (ChainCategory d),
      letI := m
      ∃ s : SymmetricCategory (ChainCategory d),
        letI := s
        ChainTensorData d m ∧
        (∀ x y : ChainCategory d, (β_ x y).hom.val = 0) ∧
        IsWeakTwoGroup (ChainCategory d) ∧ Restrained (ChainCategory d) ∧
        (∀ x : ChainCategory d, IsWeakInverse x (-x)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
