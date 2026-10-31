-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_twoBody_coefficient_sufficiency
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.twoBody_coefficient_sufficiency
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:35:32.98306+00:00
-- url     : https://prove2.me/theorems/6d28f257-70b7-4afe-be6b-2f51aeb496a8
-- title:
--   Theorem 4: coefficient sufficiency
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Let $G_2=\{P_{100},P_{010},P_{002}\}$ and let $\mathfrak g_2=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_2\}$ be its actual dynamical Lie algebra.
--
--   For real coefficients $c_{xyz}$ on the valid triples $x+y+z\le n$, put
--   $$M(c)=i\sum_{x+y+z\le n}c_{xyz}P_{xyz},\qquad \ell_\mu(c)=\sum_{a+b+c=\mu}\frac{c_{2a,2b,2c}}{a!b!c!}.$$
--
--   For $n\ge2$ and every such real coefficient family,
--   $$\left[\ell_\mu(c)=0\text{ for all }0\le2\mu\le n,\ \mu\ne1\right]\quad\Longrightarrow\quad M(c)\in\mathfrak g_2.$$
--
--   This is sufficiency for membership in the actual generated Lie algebra; no orthogonality property of that algebra is assumed.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 6, theorem4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.6,14–19, Theorem 4: sufficiency for the ACTUAL Lie closure;
no necessary-orthogonality theorem is assumed as an input. -/
theorem twoBody_coefficient_sufficiency {n : ℕ} (hn : 2 ≤ n)
    (c : ℕ → ℕ → ℕ → ℝ)
    (hc : ∀ mu : ℕ, 2 * mu ≤ n → mu ≠ 1 → centralCoefficient c mu = 0) :
    coefficientCombination n c ∈ g2 n := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
