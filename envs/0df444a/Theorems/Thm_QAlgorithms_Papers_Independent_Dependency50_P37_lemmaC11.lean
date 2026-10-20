-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_lemmaC11
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.lemmaC11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:28:29.169789+00:00
-- url     : https://prove2.me/theorems/7291f7a4-e0f6-4e68-8f81-8d9c45bf6bf1
-- title:
--   Algebra operator systems: zero capacity and scalar commutant
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Let $S_\Phi=\operatorname{span}\{K_i^*K_j\}$ be its operator system, and assume this system is closed under multiplication. Its identity membership and adjoint closure already follow from the channel. Then
--
--   $$C_{0E}(\Phi)=0\iff C_0(\Phi)=0\iff S_\Phi'=\mathbb CI.$$
--
--   The commutant uses ordinary matrix multiplication. This characterizes extinction of both classical capacities without assuming in advance that the system is full or its commutant scalar.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 26, Lemma C.11

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

/-- Lemma C.11, PDF pp.26–27: algebra hypothesis does not assume fullness or
scalar commutant, either of which would remove the theorem's content. -/
theorem lemmaC11 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (halgebra : IsOperatorAlgebra (graph Phi)) :
    (assistedCapacity Phi = 0 ↔ classicalCapacity Phi = 0) ∧
    (classicalCapacity Phi = 0 ↔
      commutant (graph Phi : Set (Operator d)) = (scalars d : Set (Operator d))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
