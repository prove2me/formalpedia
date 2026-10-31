-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P38_universality_body_threshold
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P38.universality_body_threshold
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:38:08.271984+00:00
-- url     : https://prove2.me/theorems/d2717322-9a4f-4702-a42b-653d558b62bd
-- title:
--   Corollary 1: necessary body order for universality
-- statement:
--   Let $n$ denote the number of qubits, with computational basis indexed by $\{0,1\}^n$. Write $P_{xyz}$ for the unnormalized sum of distinct phase-zero Pauli words with $x$ copies of $X$, $y$ copies of the standard $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$, and $z$ copies of $Z$. All Lie closures, linear spans, and dimensions below are over $\mathbb R$; commutators are $[A,B]=AB-BA$.
--
--   Write $\mathfrak u_n$ for the skew-Hermitian commutant of the qubit-permuting representation of $S_n$, $\mathfrak s_n$ for its total-trace-zero subalgebra, and $\mathfrak d_n=[\mathfrak u_n,\mathfrak u_n]$ for its derived algebra, equivalently the algebra with independently traceless multiplicity blocks.
--   Let $n\ge1$, $0\le k\le n$, and let $G$ be any set, finite or infinite, of Hermitian permutation-equivariant operators. Assume each member is a real linear combination of Pauli words of weight at most $k$, where weight counts nonidentity factors. If its actual real dynamical Lie algebra $\mathfrak g=\operatorname{Lie}_{\mathbb R}\{iH:H\in G\}$ is universal up to a global phase, meaning $\mathfrak s_n\subseteq\mathfrak g\subseteq\mathfrak u_n$, then
--   $$n\text{ even}\Longrightarrow k=n,\qquad n\text{ odd}\Longrightarrow k\ge n-1.$$
--
--   This is a necessary condition for arbitrary allowed generator sets; it asserts no sufficiency for those sets.
-- source:
--   On the universality of $S_n$-equivariant $k$-body gates, arXiv:2303.00728v2, PDF p. 6, corollary1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P38

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P38

open scoped BigOperators

open QAlgorithms.Papers.Independent.Support50.P30
  (QnnOperator qubitPermutationMatrix PermutationEquivariant)

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.6, Corollary 1: necessity for EVERY set of Hermitian equivariant
Pauli-degree-at-most-k generators, including infinite sets. No sufficiency for
arbitrary sets is claimed. Odd n uses k>=n-1; even n uses k=n. -/
theorem universality_body_threshold {n k : ℕ} (hn : 1 ≤ n) (hkn : k ≤ n)
    (G : Set (QnnOperator n))
    (hG : ∀ H ∈ G, H.IsHermitian ∧ PermutationEquivariant H ∧ H ∈ pauliDegreeSpace n k)
    (hU : IsEquivariantlyUniversal (generatedSkewLie G).toSubmodule) :
    (Even n → k = n) ∧ (Odd n → n - 1 ≤ k) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P38

end
