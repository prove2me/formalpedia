-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremB1
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremB1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:13:41.434743+00:00
-- url     : https://prove2.me/theorems/5dabb029-fc78-4f34-ab08-56c420f8e9f2
-- title:
--   Mixing is equivalent to eventual loss of assisted zero-error communication
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   The following three conditions are equivalent:
--
--   $$
--   \bigl[\exists k\ge1:\ C_{0E}(\Phi^k)=0\bigr]
--   \iff\bigl[\exists k\ge1:\ C_0(\Phi^k)=0\bigr]
--   \iff\Phi\text{ is mixing}.
--   $$
--
--   Mixing means convergence $\Phi^n(X)\to\operatorname{Tr}(X)\rho$ for every operator $X$, for one density $\rho$. The assisted capacity optimizes over every finite auxiliary dimension, so its vanishing uses a single time uniformly over all assisted codes.
--
--   This strengthens eventual classical scrambling to eventual failure even with prior entanglement.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 15, Theorem B.1

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

/-- Theorem B.1, PDF p.15: a SINGLE positive time kills every assisted code,
including all finite auxiliary dimensions in assistedCapacity. No erroneous
unrestricted uniform estimate on all X from the proof is assumed or asserted. -/
theorem theoremB1 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi) :
    ((∃ k : ℕ, 0 < k ∧ assistedCapacity (Nat.iterate Phi k) = 0) ↔
      EventuallyClassicalScrambling Phi) ∧
    (EventuallyClassicalScrambling Phi ↔ Mixing Phi) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
