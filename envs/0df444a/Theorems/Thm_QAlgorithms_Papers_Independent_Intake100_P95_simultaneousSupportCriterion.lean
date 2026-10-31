-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_simultaneousSupportCriterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.simultaneousSupportCriterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:51:20.16+00:00
-- url     : https://prove2.me/theorems/cb168bb4-6f17-46b7-9611-6d8a877ca169
-- title:
--   One inverter for all exact support components
-- statement:
--   Let $n\ge1$ and let $H$ be Hermitian and traceless. For each subset $S$ of qubits, let $H_S$ be the sum of the Pauli expansion terms whose nonidentity support is exactly $S$. Explicitly, for a Pauli word $P$, its coefficient is $2^{-n}\operatorname{tr}(P^\dagger H)$. Then
--
--   $$H=\sum_S H_S,\qquad H\text{ is type-I reversible}\quad\Longleftrightarrow\quad\exists K\in\mathrm{SU}(2)^{\otimes n}\ \forall S:\ KH_SK^\dagger=-H_S.$$
--
--   The same local operation must reverse all components. The components are canonical support summands, rather than arbitrary overlapping groups of monomials; zero components impose no condition.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 6, Lemma 7: simultaneous inversion of multi-qubit support components

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Lemma 7, PDF p.6, (28). Components are the canonical direct summands
of exact nonidentity support. The same K reverses every component. -/
theorem simultaneousSupportCriterion {n : ℕ} (hn : 0 < n)
    (H : Op (QAlgorithms.Qubits n)) (hH : IsHamiltonian H) :
    H = (∑ S : Finset (Fin n), supportComponent H S) ∧
    (TypeI H ↔ ∃ K : LocalSU n,
      ∀ S : Finset (Fin n), localAd K (supportComponent H S) = -supportComponent H S) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
