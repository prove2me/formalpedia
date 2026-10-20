-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremB4
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremB4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:16:01.711326+00:00
-- url     : https://prove2.me/theorems/68501042-1334-459b-b974-ab9d69e46e9a
-- title:
--   All-time ergodic classical-capacity lower bound
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Assume $\Phi$ is ergodic, meaning it has a unique invariant density. Let $r$ be the number of distinct eigenvalues of $\Phi$ on the complex unit circle. Then
--
--   $$C_0(\Phi^n)\ge\log_2 r\qquad(n\ge1).$$
--
--   The bound applies at every time; in this regime peripheral eigenvalues are simple. It supplies an all-time communication guarantee rather than only an asymptotic formula.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 16, Theorem B.4

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

/-- Theorem B.4, PDF pp.16–17: all-time bound, not merely a limit formula.
Peripheral eigenvalues are distinct and simple in the ergodic regime. -/
theorem theoremB4 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (h : Ergodic Phi) : ∀ n : ℕ, 0 < n →
      Real.logb 2 (Nat.card (peripheralEigenvalues Phi)) ≤
        classicalCapacity (Nat.iterate Phi n) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
