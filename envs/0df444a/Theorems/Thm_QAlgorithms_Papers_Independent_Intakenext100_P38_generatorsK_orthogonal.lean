-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_generatorsK_orthogonal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.generatorsK_orthogonal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:37:09.223073+00:00
-- url     : https://prove2.me/theorems/500618d7-66a8-4e56-b859-b309e7b3fc85
-- title:
--   Theorem 6: k-body central orthogonality
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   For $2\le k\le n$, let $G_k=\{P_{100},P_{010}\}\cup\{P_{00j}:2\le j\le k\}$ and $\mathfrak g_k=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_k\}$.
--
--   For $0\le2\mu\le n$, define
--   $$C_\mu=\sum_{a+b+c=\mu}\frac{(2a)!(2b)!(2c)!}{a!b!c!}P_{2a,2b,2c}.$$
--   In particular $C_0=I$.
--   For every $H\in G_k$ and every $0\le2\mu\le n$,
--   $$\left(\mu=0\ \text{or}\ \lfloor k/2\rfloor<\mu\right)\quad\Longrightarrow\quad\operatorname{Tr}(HC_\mu)=0.$$
--
--   The two cases are a union, as confirmed by the source's explanation after (39) and equation (E8). This avoids an empty literal conjunction.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 6, theorem6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.6,21, Theorem 6: 'mu=0 and high mu' enumerates a UNION of cases,
confirmed by the '(or mu=0)' explanation after (39) and by (E8). -/
theorem generatorsK_orthogonal {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (H : QnnOperator n) (hH : H ∈ generatorsK n k) (mu : ℕ)
    (hmu : 2 * mu ≤ n) (hcase : mu = 0 ∨ k / 2 < mu) :
    Matrix.trace (H * centralElement n mu) = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
