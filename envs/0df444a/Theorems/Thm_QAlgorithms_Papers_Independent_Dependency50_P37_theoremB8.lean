-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theoremB8
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theoremB8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:19:02.668371+00:00
-- url     : https://prove2.me/theorems/6ea87980-6a51-4820-853d-f45d40954ff6
-- title:
--   Four characterizations of eventual quantum scrambling
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Choose the actual peripheral decomposition $\chi(\Phi)=0\oplus\bigoplus_{k=1}^K (M_{a_k}(\mathbb C)\otimes\rho_k)$, where $K\ge1$, $a_k\ge1$, and every $\rho_k$ is a positive definite density matrix on a positive-dimensional cofactor. Here $\chi(\Phi)$ is the span of eigenoperators with eigenvalues of modulus one. The summands are embedded isometrically on mutually orthogonal subspaces of the physical system.
--
--   The following four conditions are equivalent:
--
--   $$
--   \begin{aligned}
--   &\exists n\ge1:\ Q_0(\Phi^n)=0;\\
--   &\Phi\text{ is asymptotically entanglement breaking};\\
--   &a_k=1\text{ for every }k;\\
--   &XY-YX=0\text{ for all }X,Y\in\chi(\Phi).
--   \end{aligned}
--   $$
--
--   Asymptotic entanglement breaking quantifies over all channel limits along unbounded times and every finite reference system. The last two equivalences are credited to [35, Theorem 32] through A.3.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 19, Theorem B.8

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

/-- Theorem B.8, PDF p.19: all four equivalent conditions. The last two
are imported in the paper from [35, Theorem 32] (restated as A.3). -/
theorem theoremB8 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (D : PeripheralDecomposition Phi) :
    (EventuallyQuantumScrambling Phi ↔ AsymptoticallyEntanglementBreaking Phi) ∧
    (AsymptoticallyEntanglementBreaking Phi ↔ ∀ k, D.left k = 1) ∧
    ((∀ k, D.left k = 1) ↔
      ∀ X ∈ Information100.P26.peripheral (channelMatrix Phi), ∀ Y ∈ Information100.P26.peripheral (channelMatrix Phi), X * Y - Y * X = 0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
