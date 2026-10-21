-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_proposition_2_3
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.proposition_2_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:57:31.136466+00:00
-- url     : https://prove2.me/theorems/7b209ea5-f099-4733-8cb7-984ba4f4d3fe
-- title:
--   Matrix algebras of continuous inverse algebras
-- statement:
--   Let $\mathbb K$ be a Hausdorff nondiscrete topological field and $A$ a continuous inverse $\mathbb K$-algebra: an associative unital Hausdorff topological algebra whose units form an open subset and whose inversion is continuous in the induced topology. For every matrix size $n$, equip $M_n(A)$ with its entrywise product topology. Then
--
--   $$
--   M_n(A)\text{ is a continuous inverse }\mathbb K\text{-algebra}.
--   $$
--
--   This supplies further continuous inverse algebras from matrix constructions. Commutativity of $A$ and completeness are not assumed.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 17, Proposition 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Proposition 2.3, PDF p.17: matrix algebras of CIAs are CIAs with their
natural entrywise product topology. The empty matrix case is not excluded. -/
theorem proposition_2_3
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (A : Type v) [Ring A] [Algebra K A] [TopologicalSpace A]
    (hA : continuousInverseAlgebra K A) (n : ℕ) :
    continuousInverseAlgebra K (Matrix (Fin n) (Fin n) A) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
