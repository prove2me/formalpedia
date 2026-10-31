-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_twoStep_hopping
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.twoStep_hopping
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:43:38.247074+00:00
-- url     : https://prove2.me/theorems/ded363e8-09f0-43ff-9213-1e0a962e9244
-- title:
--   Lemma 6: two-step hopping and the z=0,1 boundary
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Let $G_2=\{P_{100},P_{010},P_{002}\}$ and let $\mathfrak g_2=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_2\}$ be its actual dynamical Lie algebra.
--   Let $n\ge2$ and let $\mathfrak g$ be a real Lie algebra of skew-Hermitian matrices containing $\mathfrak g_2$. For $x+y+z\le n$, the conclusion
--   $$iP_{x,y-2,z+2}\in\mathfrak g$$
--   holds in each of these cases:
--
--   1. $y,z\ge2$ and both $iP_{xyz}$ and $iP_{x,y+2,z-2}$ lie in $\mathfrak g$.
--   2. $y\ge2$, $z\le1$, and $iP_{xyz}\in\mathfrak g$.
--
--   The second case keeps the source's special boundary clause, where the other neighbor does not exist.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 16, lemma6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.15–16, Lemma 6: includes the special z=0,1 boundary, where the
negative-index neighbor is absent. All natural subtractions are guarded. -/
theorem twoStep_hopping {n : ℕ} (hn : 2 ≤ n) (g : LieSubalgebra ℝ (QnnOperator n))
    (hg : g2 n ≤ g)
    (hskew : ∀ M : QnnOperator n, M ∈ g → M.conjTranspose = -M) :
    (∀ x y z : ℕ, x + y + z ≤ n → 2 ≤ y → 2 ≤ z →
      Complex.I • symmetricPauli n x y z ∈ g →
      Complex.I • symmetricPauli n x (y + 2) (z - 2) ∈ g →
      Complex.I • symmetricPauli n x (y - 2) (z + 2) ∈ g) ∧
    (∀ x y z : ℕ, x + y + z ≤ n → 2 ≤ y → z ≤ 1 →
      Complex.I • symmetricPauli n x y z ∈ g →
      Complex.I • symmetricPauli n x (y - 2) (z + 2) ∈ g) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
