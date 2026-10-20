-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_corollaryB11
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.corollaryB11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:20:37.624965+00:00
-- url     : https://prove2.me/theorems/7270090e-6908-4dce-b694-652c4b3eaac7
-- title:
--   Corrected refined scrambling bounds
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   The indices $q,c,c_E$ are the first positive iteration times at which the respective capacities $Q_0,C_0,C_{0E}$ vanish; an index is $+\infty$ if no such time exists.
--
--   For a mixing channel,
--
--   $$q(\Phi)\le c(\Phi)\le c_E(\Phi)\le d^2-\dim S_\Phi+1.$$
--
--   For every asymptotically entanglement-breaking channel,
--
--   $$q(\Phi)\le d^2.$$
--
--   Here $S_\Phi$ is the span of its Kraus products $K_i^*K_j$. The bounds quantify how quickly exact storage becomes impossible.
--
--   **Formalization Note** Only the refined bound changes from the print, inheriting B.10's missing $+1$. The coarse quantum bound remains unchanged because $\dim S_\Phi\ge1$.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 20, Corollary B.11

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

/-- Corollary B.11, PDF p.20, SOURCE CORRECTION: propagate B.10's +1 only
into its refined mixing bound. The coarse d^2 quantum bound remains as printed. -/
theorem corollaryB11 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi) :
    (Mixing Phi → quantumTime Phi ≤ classicalTime Phi ∧
      classicalTime Phi ≤ assistedTime Phi ∧
      assistedTime Phi ≤ (d ^ 2 - Module.finrank ℂ (graph Phi) + 1 : ℕ)) ∧
    (AsymptoticallyEntanglementBreaking Phi → quantumTime Phi ≤ (d ^ 2 : ℕ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
