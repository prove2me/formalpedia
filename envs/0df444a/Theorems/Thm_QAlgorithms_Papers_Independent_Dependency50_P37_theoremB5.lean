-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremB5
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremB5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:16:56.440615+00:00
-- url     : https://prove2.me/theorems/b08c11c1-c824-4569-9963-cee2617f6a42
-- title:
--   Classical block formula with finite attainment
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Choose the actual peripheral decomposition $\chi(\Phi)=0\oplus\bigoplus_{k=1}^K (M_{a_k}(\mathbb C)\otimes\rho_k)$, where $K\ge1$, $a_k\ge1$, and every $\rho_k$ is a positive definite density matrix on a positive-dimensional cofactor. Here $\chi(\Phi)$ is the span of eigenoperators with eigenvalues of modulus one. The summands are embedded isometrically on mutually orthogonal subspaces of the physical system.
--
--   There exists $1\le N\le d^2$ such that for every $q\ge0$,
--
--   $$\lim_{n\to\infty}C_0(\Phi^n)=C_0(\Phi^N)=C_0(\Phi^{N+q})=\log_2\sum_k a_k.$$
--
--   This identifies the eventual classical capacity and the finite time by which it is attained.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 17, Theorem B.5

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

/-- Theorem B.5, PDF pp.17–18: limit formula and finite attainment with all later shifts. -/
theorem theoremB5 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (D : PeripheralDecomposition Phi) :
    ∃ N : ℕ, 0 < N ∧ N ≤ d ^ 2 ∧
      Tendsto (fun n : ℕ => classicalCapacity (Nat.iterate Phi n)) atTop
        (nhds (classicalCapacity (Nat.iterate Phi N))) ∧
      classicalCapacity (Nat.iterate Phi N) = Real.logb 2 (peripheralBlockDimensionSum D) ∧
      ∀ q : ℕ, classicalCapacity (Nat.iterate Phi N) = classicalCapacity (Nat.iterate Phi (N + q)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
