-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_odd_coordinate_membership
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.odd_coordinate_membership
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:44:48.561652+00:00
-- url     : https://prove2.me/theorems/873e7b7c-50d5-44a4-b4ca-effd60ef7295
-- title:
--   Lemma 8: unconditional odd-coordinate membership
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Let $G_2=\{P_{100},P_{010},P_{002}\}$ and let $\mathfrak g_2=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_2\}$ be its actual dynamical Lie algebra.
--   For $n\ge2$ and $x+y+z\le n$,
--   $$x\text{ odd or }y\text{ odd or }z\text{ odd}\quad\Longrightarrow\quad iP_{xyz}\in\mathfrak g_2.$$
--
--   No seed-membership assumption is imposed. Level zero has no odd triple, while level one gives nonvacuous collective-generator membership.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 17, lemma8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.17, Lemma 8: unconditional odd-coordinate membership throughout the
valid tetrahedron, without assuming any inductively constructed seed. -/
theorem odd_coordinate_membership {n x y z : ℕ} (hn : 2 ≤ n)
    (hxyz : x + y + z ≤ n) (hodd : Odd x ∨ Odd y ∨ Odd z) :
    Complex.I • symmetricPauli n x y z ∈ g2 n := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
