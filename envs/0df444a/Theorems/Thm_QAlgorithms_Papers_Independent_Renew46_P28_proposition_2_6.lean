-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_proposition_2_6
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.proposition_2_6
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:58:33.460376+00:00
-- url     : https://prove2.me/theorems/09cd8d2f-f4b5-42d8-aa1a-43c5ea1e7db7
-- title:
--   Finite-dimensional algebras in their canonical vector topology
-- statement:
--   Let $\mathbb K$ be a Hausdorff nondiscrete topological field and $A$ a finite-dimensional associative unital $\mathbb K$-algebra. Transport the product topology on $\mathbb K^d$ along a finite basis, where $d=\dim_{\mathbb K}A$. In this canonical vector topology,
--
--   $$
--   A\text{ is a continuous inverse }\mathbb K\text{-algebra}.
--   $$
--
--   In particular, the algebra operations are continuous, the units are open, and inversion on the units is continuous. The topology is constructed from the algebra rather than supplied as an unrelated parameter.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 18, Proposition 2.6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Proposition 2.6, PDF p.18: the constructed canonical vector topology
makes every finite-dimensional unital associative algebra a CIA. -/
theorem proposition_2_6
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (A : Type v) [Ring A] [Algebra K A] [FiniteDimensional K A] :
    letI : TopologicalSpace A := canonicalFiniteVectorTopology K A
    continuousInverseAlgebra K A := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
