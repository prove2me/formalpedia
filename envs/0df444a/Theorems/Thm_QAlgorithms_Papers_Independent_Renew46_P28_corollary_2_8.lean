-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P28_corollary_2_8
-- name    : QAlgorithms.Papers.Independent.Renew46.P28.corollary_2_8
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:59:36.857079+00:00
-- url     : https://prove2.me/theorems/b5ca96e2-3021-4e4b-919d-3751ca665546
-- title:
--   Finite scalar extension of continuous inverse algebras
-- statement:
--   Let $\mathbb K$ be a Hausdorff nondiscrete topological field, $A$ a continuous inverse $\mathbb K$-algebra, and $L/\mathbb K$ a finite field extension. Give $L$ its canonical $\mathbb K$-vector topology and $L\otimes_{\mathbb K}A$ the topology transported from $A^n$ by a basis of $L$ as in Proposition 2.7. Then
--
--   $$
--   A_L=L\otimes_{\mathbb K}A\text{ is a continuous inverse }L\text{-algebra}.
--   $$
--
--   This changes the scalar field of the continuous inverse algebra while retaining its full topological-algebra structure.
-- source:
--   Lie groups over non-discrete topological fields, arXiv:math/0408008v1, PDF p. 19, Corollary 2.8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P28

namespace QAlgorithms.Papers.Independent.Renew46.P28

open Set

open scoped TensorProduct

universe u v w

/-- Corollary 2.8, PDF pp.19–20: scalar extension of a CIA along a finite
field extension is a CIA over the extension field, with the canonical topology on
that field and the finite-tensor topology on the scalar extension algebra. -/
theorem corollary_2_8
    (K : Type u) [Field K] [TopologicalSpace K] [T2Space K]
    [IsTopologicalDivisionRing K] (hK : ¬ DiscreteTopology K)
    (A : Type v) [Ring A] [Algebra K A] [TopologicalSpace A]
    (hA : continuousInverseAlgebra K A)
    (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L] :
    letI : TopologicalSpace L := canonicalFiniteVectorTopology K L
    letI : TopologicalSpace (L ⊗[K] A) :=
      finiteTensorAlgebraTopology K A (Module.finBasis K L)
    continuousInverseAlgebra L (L ⊗[K] A) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P28
