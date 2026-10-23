-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theorem1_4
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theorem1_4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:09:49.472923+00:00
-- url     : https://prove2.me/theorems/0db11c66-685f-4a4d-81c8-92735f1d57d7
-- title:
--   Simultaneous finite stabilization of classical and quantum capacities
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   There is a single integer $N$ with $1\le N\le d^2$ such that, for every integer $n\ge0$,
--
--   $$
--   Q_0(\Phi^N)=Q_0(\Phi^{N+n}),\qquad C_0(\Phi^N)=C_0(\Phi^{N+n}).
--   $$
--
--   Thus both capacity sequences attain their limiting values at the same finite time.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 3, Theorem 1.4

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

/-- Theorem 1.4, PDF p.3: one positive N works for both capacities and every later time. -/
theorem theorem1_4 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi) :
    ∃ N : ℕ, 0 < N ∧ N ≤ d ^ 2 ∧ ∀ n : ℕ,
      quantumCapacity (Nat.iterate Phi N) = quantumCapacity (Nat.iterate Phi (N + n)) ∧
      classicalCapacity (Nat.iterate Phi N) = classicalCapacity (Nat.iterate Phi (N + n)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
