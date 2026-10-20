-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_nonmixingPersistentBit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.nonmixingPersistentBit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:14:27.149892+00:00
-- url     : https://prove2.me/theorems/bff1429a-4fa5-498a-9b00-6e7fd2ef2be6
-- title:
--   Persistent perfect classical communication is exactly nonmixing
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   For every positive integer time, classical capacity stays positive exactly when the channel is nonmixing:
--
--   $$
--   \bigl[\forall n\ge1:\ C_0(\Phi^n)>0\bigr]\iff\neg\operatorname{Mixing}(\Phi).
--   $$
--
--   Here mixing is convergence on every operator to $X\mapsto\operatorname{Tr}(X)\rho$ for one invariant density $\rho$. This is the persistent-message form of B.1.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 15, §B.2, unnumbered non-mixing equivalence

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

/-- Section B.2 opening equivalence, PDF p.15: persistent positive classical capacity. -/
theorem nonmixingPersistentBit {d : ℕ} (hd : 0 < d) (Phi : Dynamics d)
    (hPhi : IsChannel Phi) :
    (∀ n : ℕ, 0 < n → 0 < classicalCapacity (Nat.iterate Phi n)) ↔ ¬ Mixing Phi := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
