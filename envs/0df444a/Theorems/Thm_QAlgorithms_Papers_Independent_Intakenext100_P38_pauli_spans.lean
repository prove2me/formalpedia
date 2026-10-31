-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_pauli_spans
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.pauli_spans
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:32:00.757999+00:00
-- url     : https://prove2.me/theorems/17a576e8-b5fc-4b2f-8aa7-92b37c527778
-- title:
--   Pauli bases of the equivariant algebras
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Write $\mathfrak u_n$ for the skew-Hermitian commutant of the qubit-permuting representation of $S_n$, $\mathfrak s_n$ for its total-trace-zero subalgebra, and $\mathfrak d_n=[\mathfrak u_n,\mathfrak u_n]$ for its derived algebra, equivalently the algebra with independently traceless multiplicity blocks.
--   For every $n\ge0$,
--   $$\mathfrak u_n=\operatorname{span}_{\mathbb R}\{iP_{xyz}:x+y+z\le n\},$$
--   $$\mathfrak s_n=\operatorname{span}_{\mathbb R}\{iP_{xyz}:0<x+y+z\le n\}.$$
--
--   These are equalities of the full algebras. At $n=0$ they give the scalar skew algebra and the zero traceless algebra, respectively.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 5, pauli-spans

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.5,10, (26)–(27)/(A4): both complete real span equalities,
including n=0 (scalar skew algebra and zero traceless algebra). -/
theorem pauli_spans (n : ℕ) :
    symmetricUnitaryAlgebra n = Submodule.span ℝ
      {A | ∃ x y z : ℕ, x + y + z ≤ n ∧ A = Complex.I • symmetricPauli n x y z} ∧
    specialSymmetricAlgebra n = Submodule.span ℝ
      {A | ∃ x y z : ℕ, 0 < x + y + z ∧ x + y + z ≤ n ∧
        A = Complex.I • symmetricPauli n x y z} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
