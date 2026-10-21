-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_proposition_E_3
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.proposition_E_3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:01:06.56342+00:00
-- url     : https://prove2.me/theorems/7cbeafac-5747-491d-8be7-5dbe19aac8c2
-- title:
--   The real smooth-curve criterion without completeness assumptions
-- statement:
--   Let $E$ be a Hausdorff metrizable real topological vector space, $U\subseteq E$ open, $F$ a Hausdorff locally convex real topological vector space and $f:U\to F$ arbitrary. In the source's extended-difference-quotient calculus,
--
--   $$
--   f\text{ is smooth}\quad\Longleftrightarrow\quad
--   f\circ\gamma\text{ is smooth for every smooth curve }\gamma:\mathbb R\to U.
--   $$
--
--   This is the real curve-testing principle. Local convexity of $E$ and completeness of either $E$ or $F$ are not assumed.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 105, Proposition E.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Proposition E.3, PDF p.105: the real smooth-curve criterion, without
completeness assumptions on either space or local convexity on the domain. -/
theorem proposition_E_3
    (E : Type v) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [TopologicalSpace.MetrizableSpace E]
    (F : Type w) [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [T2Space F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    [LocallyConvexSpace ℝ F]
    (U : Set E) (hU : IsOpen U) (f : U → F) :
    bgnCr ℝ F ⊤ U f ↔
      ∀ γ : ℝ → U,
        bgnCr ℝ E ⊤ (Set.univ : Set ℝ) (fun t => (γ t.val).val) →
        bgnCr ℝ F ⊤ (Set.univ : Set ℝ) (fun t => f (γ t.val)) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
