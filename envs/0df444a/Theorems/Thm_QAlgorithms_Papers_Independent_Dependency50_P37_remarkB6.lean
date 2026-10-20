-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_remarkB6
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.remarkB6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:17:34.738731+00:00
-- url     : https://prove2.me/theorems/cf6a4c70-1906-4c66-8966-93d909f23854
-- title:
--   Ergodic limiting capacity counts distinct peripheral eigenvalues
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Choose the actual peripheral decomposition $\chi(\Phi)=0\oplus\bigoplus_{k=1}^K (M_{a_k}(\mathbb C)\otimes\rho_k)$, where $K\ge1$, $a_k\ge1$, and every $\rho_k$ is a positive definite density matrix on a positive-dimensional cofactor. Here $\chi(\Phi)$ is the span of eigenoperators with eigenvalues of modulus one. The summands are embedded isometrically on mutually orthogonal subspaces of the physical system.
--
--   If $\Phi$ has a unique invariant density, every $a_k=1$. If $r$ counts its distinct modulus-one eigenvalues, then
--
--   $$\sum_k a_k=\dim\chi(\Phi)=r,\qquad
--   \lim_{n\to\infty}C_0(\Phi^n)=\log_2 r.$$
--
--   This is the ergodic form of B.5.
--
--   **Formalization Note** The printed display drops the exponent $n$ from $C_0(\Phi)$; the exponent is restored consistently with B.5 and the same special case on p.4.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 18, Remark B.6

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

/-- Remark B.6, PDF p.18: the printed C0(Phi) under lim_n omits the exponent.
Corrected to C0(Phi^n), as fixed unambiguously by B.5 and the p.4 special case. -/
theorem remarkB6 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (h : Ergodic Phi) (D : PeripheralDecomposition Phi) :
    (∀ k, D.left k = 1) ∧ peripheralBlockDimensionSum D = Module.finrank ℂ (Information100.P26.peripheral (channelMatrix Phi)) ∧
    Module.finrank ℂ (Information100.P26.peripheral (channelMatrix Phi)) = Nat.card (peripheralEigenvalues Phi) ∧
    Tendsto (fun n : ℕ => classicalCapacity (Nat.iterate Phi n)) atTop
      (nhds (Real.logb 2 (Nat.card (peripheralEigenvalues Phi)))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
