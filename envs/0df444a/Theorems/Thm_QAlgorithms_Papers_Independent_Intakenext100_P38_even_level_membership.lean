-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_even_level_membership
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.even_level_membership
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:45:33.919174+00:00
-- url     : https://prove2.me/theorems/62473b51-a477-4a51-b860-ccdaa0acb2c9
-- title:
--   Lemma 9: even-level weighted-zero membership
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Let $G_2=\{P_{100},P_{010},P_{002}\}$ and let $\mathfrak g_2=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_2\}$ be its actual dynamical Lie algebra.
--
--   For real coefficients $c_{xyz}$ on the valid triples $x+y+z\le n$, put
--   $$M(c)=i\sum_{x+y+z\le n}c_{xyz}P_{xyz},\qquad \ell_\mu(c)=\sum_{a+b+c=\mu}\frac{c_{2a,2b,2c}}{a!b!c!}.$$
--
--   Let $n\ge2$, $2\mu\le n$, and $\mu\ne1$. For every real coefficient family with $\ell_\mu(c)=0$,
--   $$i\sum_{a+b+c=\mu}c_{2a,2b,2c}P_{2a,2b,2c}\in\mathfrak g_2.$$
--
--   The $\mu=0$ case is retained and forces the only coefficient to zero. The factor $i$ restores the source's explicit supplementary membership convention.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 18, lemma9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.18–19, Lemma 9: i is restored using the explicit p.10 convention.
The mu=0 case is retained: its sole coefficient is forced to zero. -/
theorem even_level_membership {n mu : ℕ} (hn : 2 ≤ n) (hmu : 2 * mu ≤ n)
    (hne : mu ≠ 1) (c : ℕ → ℕ → ℕ → ℝ) (hc : centralCoefficient c mu = 0) :
    Complex.I • (∑ t ∈ levelTriples mu,
      c (2 * t.1) (2 * t.2.1) (2 * t.2.2) •
        symmetricPauli n (2 * t.1) (2 * t.2.1) (2 * t.2.2)) ∈ g2 n := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
