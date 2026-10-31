-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_center_pauli_span
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.center_pauli_span
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:33:33.829494+00:00
-- url     : https://prove2.me/theorems/25e1747a-987e-415f-949a-01774a24cb05
-- title:
--   Proposition 1: Pauli description of the center
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Write $\mathfrak u_n$ for the skew-Hermitian commutant of the qubit-permuting representation of $S_n$, $\mathfrak s_n$ for its total-trace-zero subalgebra, and $\mathfrak d_n=[\mathfrak u_n,\mathfrak u_n]$ for its derived algebra, equivalently the algebra with independently traceless multiplicity blocks.
--
--   For $0\le2\mu\le n$, define
--   $$C_\mu=\sum_{a+b+c=\mu}\frac{(2a)!(2b)!(2c)!}{a!b!c!}P_{2a,2b,2c}.$$
--   In particular $C_0=I$.
--   For every $n\ge0$,
--   $$\mathfrak z(\mathfrak u_n)=\operatorname{span}_{\mathbb R}\{iC_\mu:0\le\mu\le\lfloor n/2\rfloor\}.$$
--
--   The formula includes the identity direction. The source's note on page 13 attributes a more general version to Proposition 1 of Ref. [18].
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 5, proposition1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.5,11, Proposition 1, (29)/(B1). Includes C_0=I.
The p.13 note credits the more general Proposition 1 of Ref.[18]. -/
theorem center_pauli_span (n : ℕ) :
    algebraCenter (symmetricUnitaryAlgebra n) =
      Submodule.span ℝ {A | ∃ mu : ℕ, 2 * mu ≤ n ∧
        A = Complex.I • centralElement n mu} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
