-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_twoBody_orthogonal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.twoBody_orthogonal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:41:34.166764+00:00
-- url     : https://prove2.me/theorems/8d9203fb-c602-4d9d-8c70-ff9426dad1c7
-- title:
--   Corollary 3: orthogonality of the full Lie closure
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Let $G_2=\{P_{100},P_{010},P_{002}\}$ and let $\mathfrak g_2=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_2\}$ be its actual dynamical Lie algebra.
--
--   For $0\le2\mu\le n$, define
--   $$C_\mu=\sum_{a+b+c=\mu}\frac{(2a)!(2b)!(2c)!}{a!b!c!}P_{2a,2b,2c}.$$
--   In particular $C_0=I$.
--   For $n\ge2$, every $M\in\mathfrak g_2$, and each $0\le2\mu\le n$ with $\mu\ne1$,
--   $$\operatorname{Tr}(MC_\mu)=0.$$
--
--   Here $M$ is already skew-Hermitian. The conclusion covers all nested commutators and real combinations, rather than just the original generators.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 14, corollary3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.14, Corollary 3: orthogonality for every matrix in the full Lie closure.
M is already skew-Hermitian; no additional factor i is inserted. -/
theorem twoBody_orthogonal {n : ℕ} (hn : 2 ≤ n)
    (M : QnnOperator n) (hM : M ∈ g2 n) (mu : ℕ) (hmu : 2 * mu ≤ n) (hne : mu ≠ 1) :
    Matrix.trace (M * centralElement n mu) = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
