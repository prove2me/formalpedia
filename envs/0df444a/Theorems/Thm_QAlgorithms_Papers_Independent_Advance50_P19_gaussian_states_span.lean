-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_gaussian_states_span
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.gaussian_states_span
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:59:21.526984+00:00
-- url     : https://prove2.me/theorems/9ab90c58-b4eb-4211-9344-f447283dc48f
-- title:
--   Gaussian fermionic densities span physical densities
-- statement:
--   Fix an $n$-mode CAR representation on its $2^n$-dimensional Fock space. Let $\rho$ be positive, trace one, and commute with total parity. There exist a finite number $k$ of normalized Gaussian fermionic density matrices $\sigma_1,\ldots,\sigma_k$ and real coefficients $a_1,\ldots,a_k$ such that
--
--   $$\rho=\sum_{j=1}^{k}a_j\sigma_j.$$
--
--   Both even- and odd-parity pure Gaussian states are admitted. Coefficients may have either sign. This is a real linear-span statement for physical densities, and does not claim that even densities span odd operators.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 8, Lemma S5

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Lemma S5: real linear span of normalized Gaussian FERMIONIC
states; the claim ranges over parity-preserving densities, not all qubit
matrices. Both Gaussian parity sectors and signed real coefficients are allowed. -/
theorem gaussian_states_span {n : ℕ} (s : CARSystem n)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsFermionicState s rho) :
    ∃ (k : ℕ) (a : Fin k → ℝ)
      (sigma : Fin k → Matrix (Qubits n) (Qubits n) ℂ),
      (∀ j, IsGaussianState s (sigma j)) ∧
        rho = ∑ j, (a j : ℂ) • sigma j := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
