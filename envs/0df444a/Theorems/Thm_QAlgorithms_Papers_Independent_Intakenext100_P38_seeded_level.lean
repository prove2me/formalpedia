-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_seeded_level
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.seeded_level
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:44:07.000836+00:00
-- url     : https://prove2.me/theorems/d5a6b4fd-1944-4b05-a40e-f08c58809209
-- title:
--   Lemma 7: propagation from the three printed seeds
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Let $G_2=\{P_{100},P_{010},P_{002}\}$ and let $\mathfrak g_2=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_2\}$ be its actual dynamical Lie algebra.
--   Let $n\ge2$ and $1\le k\le n$. Assume $iP_{k-1,1,0}$, $iP_{0,k-1,1}$, and $iP_{1,0,k-1}$ all belong to $\mathfrak g_2$. Then
--   $$x+y+z=k,\quad(x\text{ odd or }y\text{ odd or }z\text{ odd})\quad\Longrightarrow\quad iP_{xyz}\in\mathfrak g_2.$$
--   In particular, if $k$ is odd, every triple at level $k$ has this membership.
--
--   This conditional result retains all three seeds exactly as printed in the lemma, even though symmetry can make them redundant.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 16, lemma7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.16–17, Lemma 7: the three printed seeds, the odd-coordinate
conclusion, and the explicit odd-level consequence are all retained. -/
theorem seeded_level {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hX : Complex.I • symmetricPauli n (k - 1) 1 0 ∈ g2 n)
    (hY : Complex.I • symmetricPauli n 0 (k - 1) 1 ∈ g2 n)
    (hZ : Complex.I • symmetricPauli n 1 0 (k - 1) ∈ g2 n) :
    (∀ x y z : ℕ, x + y + z = k → (Odd x ∨ Odd y ∨ Odd z) →
      Complex.I • symmetricPauli n x y z ∈ g2 n) ∧
    (Odd k → ∀ x y z : ℕ, x + y + z = k →
      Complex.I • symmetricPauli n x y z ∈ g2 n) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
