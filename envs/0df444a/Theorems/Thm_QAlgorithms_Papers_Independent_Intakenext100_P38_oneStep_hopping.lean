-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_oneStep_hopping
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.oneStep_hopping
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:43:09.033026+00:00
-- url     : https://prove2.me/theorems/fb4f8d13-a647-475d-923d-6af8c66a3248
-- title:
--   Lemma 5: one-step hopping with all boundary clauses
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Let $G_2=\{P_{100},P_{010},P_{002}\}$ and let $\mathfrak g_2=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_2\}$ be its actual dynamical Lie algebra.
--   Let $n\ge2$ and let $\mathfrak g$ be a real Lie algebra of skew-Hermitian matrices containing $\mathfrak g_2$. For valid triples, write $P_{xyz}\in_i\mathfrak g$ to mean $iP_{xyz}\in\mathfrak g$. Then:
--
--   1. If $x+y+z\le n$, $y,z\ge1$, and $P_{xyz},P_{x,y+1,z-1}\in_i\mathfrak g$, then $P_{x,y-1,z+1}\in_i\mathfrak g$.
--   2. If $x+y\le n$, $y\ge1$, and $P_{xy0}\in_i\mathfrak g$, then $P_{x,y-1,1}\in_i\mathfrak g$.
--   3. If $1\le x\le n$ and $P_{x00}\in_i\mathfrak g$, then $P_{x-1,1,0}\in_i\mathfrak g$.
--
--   The first conclusion is the displayed hopping rule
--   $$iP_{x,y-1,z+1}\in\mathfrak g.$$
--   These rules retain the collective-generator assumption used by the proof and the two boundary cases.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 16, lemma5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.15–16, Lemma 5: all three boundary clauses. The standing hypothesis
g2<=g supplies the collective one-body generators used by the proof. -/
theorem oneStep_hopping {n : ℕ} (hn : 2 ≤ n) (g : LieSubalgebra ℝ (QnnOperator n))
    (hg : g2 n ≤ g)
    (hskew : ∀ M : QnnOperator n, M ∈ g → M.conjTranspose = -M) :
    (∀ x y z : ℕ, x + y + z ≤ n → 1 ≤ y → 1 ≤ z →
      Complex.I • symmetricPauli n x y z ∈ g →
      Complex.I • symmetricPauli n x (y + 1) (z - 1) ∈ g →
      Complex.I • symmetricPauli n x (y - 1) (z + 1) ∈ g) ∧
    (∀ x y : ℕ, x + y ≤ n → 1 ≤ y →
      Complex.I • symmetricPauli n x y 0 ∈ g →
      Complex.I • symmetricPauli n x (y - 1) 1 ∈ g) ∧
    (∀ x : ℕ, x ≤ n → 1 ≤ x →
      Complex.I • symmetricPauli n x 0 0 ∈ g →
      Complex.I • symmetricPauli n (x - 1) 1 0 ∈ g) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
