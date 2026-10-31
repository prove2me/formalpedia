-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P06_strictSkeletalCriterion
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P06.strictSkeletalCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T22:51:25.458991+00:00
-- url     : https://prove2.me/theorems/d64eac0d-7de4-491f-b5f6-eaf7a512e892
-- title:
--   Zero Sính class characterizes simultaneous strict and skeletal replacement
-- statement:
--   Let $\mathcal C$ be a Gr-category. Compute its associator cochain $a$ from its actual canonical skeleton with the full transported monoidal structure, using left coordinates and the associated conjugation action. Then
--
--   $$
--   \bigl(\exists f:\operatorname{Sk}(\mathcal C)^2\to\operatorname{Aut}(I),\ a=df\bigr)
--   \iff
--   \bigl(\exists\mathcal D\text{ strict and skeletal Gr-category},\
--   \mathcal C\simeq_{\otimes}\mathcal D\bigr).
--   $$
--
--   Here $df(x,y,z)=\rho(x)f(y,z)-f(xy,z)+f(x,yz)-f(x,y)$; thus the left side is precisely vanishing of the Sính class. Weak-inverse witnesses for the constructed skeleton are supplied as part of the conclusion. The right side requires both strictness and skeletality on the same representative and uses full monoidal equivalence.
--
--   This distinguishes ordinary strictification from vanishing of the associator invariant.
-- source:
--   Hoàng Xuân Sính's Thesis: Categorifying Group Theory, arXiv:2308.05119v2, PDF p. 9, §4: zero Sính class iff strict and skeletal representative

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P06

namespace QAlgorithms.Papers.Independent.Intakenext100.P06

open CategoryTheory CategoryTheory.MonoidalCategory

open QAlgorithms.Papers.Independent.Gap48.P14

open QAlgorithms.Papers.Independent.Renew46.P18

universe u v u1 v1 w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P06.singletonSymmetric

/-- Section 4, PDF p. 9: zero Sinh class if and only if there is a
simultaneously strict and skeletal representative. Zero class is expressed
by the actual associator cochain of Mathlib's transported skeleton being
a coboundary. The skeleton and all its coherence are constructed, not
an arbitrary space or invariant supplied as a hypothesis. Strictness alone
on an unrelated representative is never used to define this condition. -/
theorem strictSkeletalCriterion {C : Type u} [Category.{v} C]
    [MonoidalCategory C] (h : IsWeakTwoGroup C) :
    (∃ hs : IsWeakTwoGroup (Skeleton C),
      ∃ f : Skeleton C → Skeleton C → Aut (𝟙_ (Skeleton C)),
        ∀ x y z : Skeleton C,
          associatorCoordinate hs (skeleton_skeletal C) x y z =
            pulledCoboundary hs id f x y z) ↔
    ∃ (D : Type u) (cat : Category.{v} D),
      letI := cat
      ∃ m : MonoidalCategory D,
        letI := m
        IsWeakTwoGroup D ∧ Skeletal D ∧ StrictCoherence D ∧
          Nonempty (GrEquivalence C D) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P06
