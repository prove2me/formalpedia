-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_equivariant_dimension
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.equivariant_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:32:39.314219+00:00
-- url     : https://prove2.me/theorems/e25b4aa6-b8f0-4178-b0c0-d73fa94a253d
-- title:
--   Dimension of the equivariant algebra
-- statement:
--   Write $\mathfrak u_n$ for the skew-Hermitian commutant of the qubit-permuting representation of $S_n$, $\mathfrak s_n$ for its total-trace-zero subalgebra, and $\mathfrak d_n=[\mathfrak u_n,\mathfrak u_n]$ for its derived algebra, equivalently the algebra with independently traceless multiplicity blocks.
--   For every $n\ge0$,
--   $$\dim_{\mathbb R}\mathfrak u_n=\binom{n+3}{3}.$$
--   Here the representation permutes $n$ qubits, and the ambient matrices have dimension $2^n$ over $\mathbb C$.
--
--   This is the tetrahedral dimension formula for permutation-equivariant skew operators.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 10, equivariant-dimension

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.10, Note A: real dimension is the (n+1)st tetrahedral number. -/
theorem equivariant_dimension (n : ℕ) :
    Module.finrank ℝ (symmetricUnitaryAlgebra n) = (n + 3).choose 3 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
