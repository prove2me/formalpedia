-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_centerless_coefficients
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.centerless_coefficients
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:34:11.787096+00:00
-- url     : https://prove2.me/theorems/6ea8bc41-48ab-4a34-8ad0-505f7dc3317e
-- title:
--   Characterization of centerless coefficients
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Write $\mathfrak u_n$ for the skew-Hermitian commutant of the qubit-permuting representation of $S_n$, $\mathfrak s_n$ for its total-trace-zero subalgebra, and $\mathfrak d_n=[\mathfrak u_n,\mathfrak u_n]$ for its derived algebra, equivalently the algebra with independently traceless multiplicity blocks.
--
--   For real coefficients $c_{xyz}$ on the valid triples $x+y+z\le n$, put
--   $$M(c)=i\sum_{x+y+z\le n}c_{xyz}P_{xyz},\qquad \ell_\mu(c)=\sum_{a+b+c=\mu}\frac{c_{2a,2b,2c}}{a!b!c!}.$$
--
--   For any complex $2^n\times2^n$ matrix $A$,
--   $$A\in\mathfrak d_n\quad\Longleftrightarrow\quad \exists c\text{ real}:\ A=M(c)\ \text{and}\ \ell_\mu(c)=0\quad(0\le2\mu\le n).$$
--
--   This describes the independent special-unitary block algebra, including the $\mu=0$ trace condition, in Pauli coordinates.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 5, centerless-coefficients

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.5, (30)–(31): BOTH directions, including mu=0 (trace zero).
The left side uses the intrinsic derived algebra, not the coefficient condition. -/
theorem centerless_coefficients (n : ℕ) (A : QnnOperator n) :
    A ∈ centerlessSymmetricAlgebra n ↔
      ∃ c : ℕ → ℕ → ℕ → ℝ, A = coefficientCombination n c ∧
        ∀ mu : ℕ, 2 * mu ≤ n → centralCoefficient c mu = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
