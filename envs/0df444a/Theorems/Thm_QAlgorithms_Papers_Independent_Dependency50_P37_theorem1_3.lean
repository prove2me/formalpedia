-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theorem1_3
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theorem1_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T15:09:09.519884+00:00
-- url     : https://prove2.me/theorems/851afbb0-2a60-48ee-9cf0-f84e59390c22
-- title:
--   Quadratic quantum scrambling bound
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   The indices $q,c,c_E$ are the first positive iteration times at which the respective capacities $Q_0,C_0,C_{0E}$ vanish; an index is $+\infty$ if no such time exists.
--
--   If $\Phi$ is eventually quantum scrambling, then
--
--   $$q(\Phi)\le d^2.$$
--
--   This is the uniform dimension bound on the loss of perfect quantum storage.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 3, Theorem 1.3

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

/-- Theorem 1.3, PDF p.3. -/
theorem theorem1_3 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (h : EventuallyQuantumScrambling Phi) : quantumTime Phi ≤ (d ^ 2 : ℕ) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
