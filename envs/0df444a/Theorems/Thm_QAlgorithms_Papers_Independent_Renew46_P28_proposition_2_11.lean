-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_proposition_2_11
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.proposition_2_11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:59:59.661432+00:00
-- url     : https://prove2.me/theorems/db2e1733-95e6-4ee1-8414-349ec9053600
-- title:
--   Locally finite countable-dimensional algebras in the finite topology
-- statement:
--   Let $\mathbb K$ be a Hausdorff nondiscrete locally compact topological field, and $A$ an associative unital $\mathbb K$-algebra of at most countable vector-space dimension. Assume that every finite subset of $A$ lies in a finite-dimensional unital subalgebra. Give $A$ the finite topology: the final topology for the inclusions of all finite-dimensional vector subspaces with their canonical vector topologies. Then
--
--   $$
--   A\text{ is a continuous inverse }\mathbb K\text{-algebra}.
--   $$
--
--   This covers finite-dimensional algebras as well as countably infinite-dimensional locally finite algebras. The final topology is constructed using every finite-dimensional subspace.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 20, Proposition 2.11

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Proposition 2.11, PDF p.20: countable-dimensional locally finite unital
associative algebras over locally compact topological fields are CIAs in the
finite topology; finite dimension is allowed. -/
theorem proposition_2_11
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] [LocallyCompactSpace K]
    (hK : ¬ DiscreteTopology K)
    (A : Type v) [Ring A] [Algebra K A]
    (hcountable : Module.rank K A ≤ Cardinal.aleph0)
    (hfinite : locallyFiniteAlgebra K A) :
    letI : TopologicalSpace A := finiteTopology K A
    continuousInverseAlgebra K A := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
