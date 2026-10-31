-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_twoBody_dimension
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.twoBody_dimension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:36:02.560236+00:00
-- url     : https://prove2.me/theorems/69da1ec5-4b05-43eb-805c-9fc2de6ffd13
-- title:
--   Dimension of the two-body dynamical algebra
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Let $G_2=\{P_{100},P_{010},P_{002}\}$ and let $\mathfrak g_2=\operatorname{Lie}_{\mathbb R}\{iH:H\in G_2\}$ be its actual dynamical Lie algebra.
--   For $n\ge2$,
--   $$\dim_{\mathbb R}\mathfrak g_2=\binom{n+3}{3}-\lfloor n/2\rfloor.$$
--
--   The dimension deficit counts all absent central directions, including the scalar identity direction.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 6, dimension-g2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.6,19, (35): the two-body dimension; n>=2 guards the central line. -/
theorem twoBody_dimension {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank ℝ (g2 n) = (n + 3).choose 3 - n / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
