-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_specialCases
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.specialCases
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:12:07.548247+00:00
-- url     : https://prove2.me/theorems/53a4e67a-2368-4f67-8914-6029398ac7f9
-- title:
--   Classical and unique-fixed-state peripheral special cases
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Choose the actual peripheral decomposition $\chi(\Phi)=0\oplus\bigoplus_{k=1}^K (M_{a_k}(\mathbb C)\otimes\rho_k)$, where $K\ge1$, $a_k\ge1$, and every $\rho_k$ is a positive definite density matrix on a positive-dimensional cofactor. Here $\chi(\Phi)$ is the span of eigenoperators with eigenvalues of modulus one. The summands are embedded isometrically on mutually orthogonal subspaces of the physical system.
--
--   If $\Phi(X)=\operatorname{diag}(A\operatorname{diag}X)$ for a nonnegative column-stochastic matrix $A$, every $a_k=1$, and
--
--   $$
--   \sum_k a_k=\dim\chi(\Phi)=\#\{\text{peripheral eigenvalues of }A\text{, with multiplicity}\},
--   \qquad \lim_n C_0(\Phi^n)=\log_2\dim\chi(\Phi).
--   $$
--
--   If instead $\Phi$ has a unique invariant density, every $a_k=1$ and the same displayed capacity limit holds.
--
--   These are the two stated reductions of the general block formula. In the classical clause the peripheral vector-space dimension counts multiplicities, rather than just distinct eigenvalues.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 4, §1.1, unnumbered special cases

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

/-- Special cases after Theorem 1.5, PDF p.4: classical multiplicities and the unique
fixed-state case. Geometric peripheral dimension equals algebraic multiplicity
for stochastic matrices; distinct-spectrum cardinality is reserved for ergodic channels. -/
theorem specialCases {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (D : PeripheralDecomposition Phi) :
    (∀ A : Operator d, ColumnStochastic A → Phi = Information100.P62.classicalChannel (A.map Complex.re) →
      (∀ k, D.left k = 1) ∧
      peripheralBlockDimensionSum D = Module.finrank ℂ (Information100.P26.peripheral (channelMatrix Phi)) ∧
      Module.finrank ℂ (Information100.P26.peripheral (channelMatrix Phi)) = Module.finrank ℂ (matrixPeripheral A) ∧
      Tendsto (fun n : ℕ => classicalCapacity (Nat.iterate Phi n)) atTop
        (nhds (Real.logb 2 (Module.finrank ℂ (Information100.P26.peripheral (channelMatrix Phi)))))) ∧
    (Ergodic Phi → (∀ k, D.left k = 1) ∧
      Tendsto (fun n : ℕ => classicalCapacity (Nat.iterate Phi n)) atTop
        (nhds (Real.logb 2 (Module.finrank ℂ (Information100.P26.peripheral (channelMatrix Phi)))))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
