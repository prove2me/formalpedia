-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_skeletalReplacement
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.skeletalReplacement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:46:23.367398+00:00
-- url     : https://prove2.me/theorems/f1e6fc89-4817-43ce-aa5e-82dac3e2fed2
-- title:
--   Every Gr-category has a skeletal replacement
-- statement:
--   Let $\mathcal C$ be a monoidal category whose arrows are invertible and whose objects have two-sided tensor inverses up to isomorphism. Equip its canonical skeleton $\operatorname{Sk}(\mathcal C)$ with the full monoidal structure transported along the skeleton equivalence. Then
--
--   $$
--   \operatorname{Sk}(\mathcal C)\text{ is a skeletal Gr-category},\qquad
--   \operatorname{Sk}(\mathcal C)\simeq_{\otimes}\mathcal C.
--   $$
--
--   The comparison is the actual skeleton equivalence with strong monoidal structures in both directions and monoidal unit and counit isomorphisms. This permits removing redundant isomorphic objects while retaining all monoidal coherence.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 19, Appendix A, Theorem 13: skeletal replacement

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Theorem 13, PDF p. 19 (also Section 3, p. 7): the actual Mathlib
skeleton with its transported full monoidal structure is a skeletal
Gr-category; the comparison is the skeleton equivalence itself. -/
theorem skeletalReplacement {C : Type u} [Category.{v} C]
    [MonoidalCategory C] (h : IsWeakTwoGroup C) :
    Skeletal (Skeleton C) ∧ IsWeakTwoGroup (Skeleton C) ∧
      ∃ E : GrEquivalence (Skeleton C) C, E.e = skeletonEquivalence C := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
