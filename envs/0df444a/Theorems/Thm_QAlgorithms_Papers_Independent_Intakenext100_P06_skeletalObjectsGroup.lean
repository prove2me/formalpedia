-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_skeletalObjectsGroup
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.skeletalObjectsGroup
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:49:42.695239+00:00
-- url     : https://prove2.me/theorems/c38d393c-1c26-4a51-a489-53891b774da4
-- title:
--   Actual skeletal objects form a group
-- statement:
--   Let $\mathcal C$ be a skeletal Gr-category. Its actual object set, without passage to a quotient, carries a group structure such that
--
--   $$
--   x\cdot y=x\otimes y,\qquad 1=I,\qquad x^{-1}=y
--   \quad\text{whenever }x\otimes y\cong I\cong y\otimes x.
--   $$
--
--   Skeletality means that isomorphic objects are equal. This identifies the group law and every possible weak inverse with the original monoidal data.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 7, §3: actual objects of a skeletal Gr-category form a group

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Section 3, PDF p. 7: the group is on actual skeletal objects,
with exactly the given tensor product and unit, rather than a quotient. -/
theorem skeletalObjectsGroup {C : Type u} [Category.{v} C]
    [MonoidalCategory C] (h : IsWeakTwoGroup C) (hs : Skeletal C) :
    ∃ k : Group C,
      letI := k
      (∀ x y : C, x * y = x ⊗ y) ∧ (1 : C) = 𝟙_ C ∧
      (∀ x y : C, IsWeakInverse x y → x⁻¹ = y) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
