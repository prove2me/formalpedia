-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_twoBody_axis_invariant
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.twoBody_axis_invariant
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:42:13.853278+00:00
-- url     : https://prove2.me/theorems/105a119a-925b-4e1d-bb40-9c3a2f2440f7
-- title:
--   Lemma 4: invariance under axis interchanges
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Let $G_2=\{P_{100},P_{010},P_{002}\}$ and let $\mathfrak g_2=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_2\}$ be its actual dynamical Lie algebra.
--   For a permutation $\sigma$ of the three axes, let $T_\sigma$ be the complex-linear map that sends each full tensor Pauli word to the word obtained by applying $\sigma$ on each nonidentity factor, fixing every identity factor. For $n\ge2$,
--   $$T_\sigma(\mathfrak g_2)=\mathfrak g_2.$$
--
--   The map is defined on the entire Pauli-word basis; an odd axis permutation is not assumed to be unitary conjugation.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 15, lemma4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.15, Lemma 4: exact subspace invariance under any axis permutation;
the map acts on full Pauli-word coefficients and fixes the identity label. -/
theorem twoBody_axis_invariant {n : ℕ} (hn : 2 ≤ n) (sigma : Equiv.Perm (Fin 3)) :
    axisRelabel (n := n) sigma '' (g2 n : Set (QnnOperator n)) = (g2 n : Set (QnnOperator n)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
