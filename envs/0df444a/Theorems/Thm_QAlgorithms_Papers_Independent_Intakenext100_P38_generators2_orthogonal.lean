-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_generators2_orthogonal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.generators2_orthogonal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:34:50.904013+00:00
-- url     : https://prove2.me/theorems/04ebf1b5-0735-4920-9f57-a75815679085
-- title:
--   Theorem 3: generator orthogonality
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Let $G_2=\{P_{100},P_{010},P_{002}\}$ and let $\mathfrak g_2=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_2\}$ be its actual dynamical Lie algebra.
--
--   For $0\le2\mu\le n$, define
--   $$C_\mu=\sum_{a+b+c=\mu}\frac{(2a)!(2b)!(2c)!}{a!b!c!}P_{2a,2b,2c}.$$
--   In particular $C_0=I$.
--   If $n\ge2$, $H\in G_2$, $0\le2\mu\le n$, and $\mu\ne1$, then
--   $$\operatorname{Tr}(HC_\mu)=0.$$
--
--   This is a statement about the original Hermitian generators, so $H$ carries no extra factor of $i$. It identifies their missing central projections.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 5, theorem3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.5,14, Theorem 3: H is Hermitian, so there is no extra i on H. -/
theorem generators2_orthogonal {n : ℕ} (hn : 2 ≤ n)
    (H : QnnOperator n) (hH : H ∈ generators2 n) (mu : ℕ)
    (hmu : 2 * mu ≤ n) (hne : mu ≠ 1) :
    Matrix.trace (H * centralElement n mu) = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
