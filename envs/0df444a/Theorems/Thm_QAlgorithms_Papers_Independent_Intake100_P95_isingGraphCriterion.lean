-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_isingGraphCriterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.isingGraphCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:49:50.456843+00:00
-- url     : https://prove2.me/theorems/998aa573-2479-40be-b6a7-37900532fa7c
-- title:
--   Ising inversion and bipartite coupling topology
-- statement:
--   Let $n\ge1$ and let $J_{k\ell}\in\mathbb R$ be coupling weights for $k<\ell$. Assume the graph on the $n$ qubits, with an edge precisely where $J_{k\ell}\ne0$, is connected. Embed each Pauli operator by identities on the remaining qubits and put
--
--   $$H_{ZZ}=\frac\pi2\sum_{k<\ell}J_{k\ell}Z_kZ_\ell.$$
--
--   Then $H_{ZZ}$ is type-I locally reversible if and only if its support graph is bipartite. Type-I means one tensor product of special-unitary single-qubit operations reverses the evolution for every real time. Couplings may have either sign; completeness of the graph is not assumed.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 5, Lemma 5 (Variant to Beth [13]): ZZ coupling graph

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Lemma 5, PDF pp.5–6, (25): real signed nonzero couplings define edges;
the section assumes connected support, but never a complete graph. -/
theorem isingGraphCriterion {n : ℕ} (hn : 0 < n)
    (J : Fin n → Fin n → ℝ) (hconnected : (couplingGraph J).Connected) :
    TypeI (isingZZ J) ↔ BipartiteCouplings J := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
