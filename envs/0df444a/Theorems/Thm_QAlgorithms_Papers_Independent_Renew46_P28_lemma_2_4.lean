-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_lemma_2_4
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.lemma_2_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:57:59.520189+00:00
-- url     : https://prove2.me/theorems/0e26cf42-9608-4dc6-bf8f-490ec1359896
-- title:
--   Units in finite-dimensional unital subalgebras
-- statement:
--   Let $\mathbb K$ be the source's Hausdorff nondiscrete topological field, $A$ a finite-dimensional associative unital $\mathbb K$-algebra, and $B\subseteq A$ a unital subalgebra with the same identity. Identifying its units with their values in $A$, one has
--
--   $$
--   B^\times=A^\times\cap B.
--   $$
--
--   Thus ambient invertibility of an element of $B$ is already invertibility in $B$. Finite-dimensionality is assumed on $A$; no topology on $A$ is needed for this algebraic statement.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 17, Lemma 2.4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Lemma 2.4, PDF p.17: a unital subalgebra of a finite-dimensional unital
associative algebra has exactly the ambient units which lie in it. -/
theorem lemma_2_4
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (A : Type v) [Ring A] [Algebra K A] [FiniteDimensional K A]
    (B : Subalgebra K A) :
    (Subtype.val '' {b : B | IsUnit b} : Set A) =
      {a : A | IsUnit a} ∩ (B : Set A) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
