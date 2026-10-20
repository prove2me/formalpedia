-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremB7
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremB7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:18:12.117366+00:00
-- url     : https://prove2.me/theorems/2ec21b06-ec38-46cd-9002-50418a4cb9c5
-- title:
--   Quantum block formula with finite attainment
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Choose the actual peripheral decomposition $\chi(\Phi)=0\oplus\bigoplus_{k=1}^K (M_{a_k}(\mathbb C)\otimes\rho_k)$, where $K\ge1$, $a_k\ge1$, and every $\rho_k$ is a positive definite density matrix on a positive-dimensional cofactor. Here $\chi(\Phi)$ is the span of eigenoperators with eigenvalues of modulus one. The summands are embedded isometrically on mutually orthogonal subspaces of the physical system.
--
--   There exists $1\le N\le d^2$ such that for every $q\ge0$,
--
--   $$\lim_{n\to\infty}Q_0(\Phi^n)=Q_0(\Phi^N)=Q_0(\Phi^{N+q})=\log_2\max_k a_k.$$
--
--   Correctability means a single recovery channel reverses $\Phi$ on every density supported in the encoding subspace. This gives the exact eventual quantum storage capacity.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 18, Theorem B.7

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

/-- Theorem B.7, PDF pp.18–19: the imported quantumCapacity uses the equivalent
Knill–Laflamme subspace condition (A.7–A.9), covering every supported density
with one recovery channel. The block maximum is nonempty. -/
theorem theoremB7 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (D : PeripheralDecomposition Phi) :
    ∃ N : ℕ, 0 < N ∧ N ≤ d ^ 2 ∧
      Tendsto (fun n : ℕ => quantumCapacity (Nat.iterate Phi n)) atTop
        (nhds (quantumCapacity (Nat.iterate Phi N))) ∧
      quantumCapacity (Nat.iterate Phi N) = Real.logb 2 (blockMaximum D) ∧
      ∀ q : ℕ, quantumCapacity (Nat.iterate Phi N) = quantumCapacity (Nat.iterate Phi (N + q)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
