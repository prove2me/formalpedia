-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P10_boundsAndFaithfulness
-- name    : QAlgorithms.Papers.Independent.Information100.P10.boundsAndFaithfulness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:37:43.598573+00:00
-- url     : https://prove2.me/theorems/0e21f43c-12cf-4c01-bc1d-9fe2013c3645
-- title:
--   ED bounds and faithfulness: property i
-- statement:
--   Let $\psi$ be a normalized pure state of $M$ qubits. Write $r_\mu$ for its local Bloch expectation vector, $E_\mu=1-\|r_\mu\|_2^2$, and $E$ for the geometrically defined entanglement distance. Then
--
--   $$0\le E_\mu\le1\quad(\mu=0,\ldots,M-1),\qquad 0\le E(\psi)\le M,\qquad E(\psi)=0\iff\psi\text{ is fully separable}.$$
--
--   Here full separability means a tensor product of normalized single-qubit states up to a complex scalar of modulus one, including the empty tensor product when $M=0$. Thus ED detects pure-state full separability in both directions; the upper bound does not assert attainment for every register size.
-- source:
--   Geometric Aspects of Entanglement, arXiv:2610.03446v1, PDF p. 4, ED bounds and faithfulness: property i

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P10

namespace QAlgorithms.Papers.Independent.Information100.P10

open scoped ComplexConjugate

/-- PDF p.4, property i: local and total bounds and both directions of full separability. -/
theorem boundsAndFaithfulness {M : ℕ} (psi : Ket M) (hpsi : IsState psi) :
    (∀ q, 0 ≤ localED psi q ∧ localED psi q ≤ 1) ∧
    (0 ≤ entanglementDistance psi ∧ entanglementDistance psi ≤ (M : ℝ)) ∧
    (entanglementDistance psi = 0 ↔ FullySeparable psi) := by sorry

end QAlgorithms.Papers.Independent.Information100.P10
