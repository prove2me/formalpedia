-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_theorem1_2
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.theorem1_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:08:24.582512+00:00
-- url     : https://prove2.me/theorems/d3d3f5f4-1cf4-4498-b897-5919b9e12ce2
-- title:
--   Quadratic scrambling bound and a dimension-indexed sharp family
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   The indices $q,c,c_E$ are the first positive iteration times at which the respective capacities $Q_0,C_0,C_{0E}$ vanish; an index is $+\infty$ if no such time exists.
--
--   If $\Phi$ is eventually classical scrambling, then
--
--   $$q(\Phi)\le c(\Phi)\le d^2.$$
--
--   Moreover, for every $d\ge1$ there is a channel $\Psi$ on $M_d(\mathbb C)$ such that
--
--   $$c(\Psi)=\left\lceil\frac{d^2-2d+2}{2}\right\rceil.$$
--
--   The second assertion certifies the quadratic dimension dependence. For $d=1$ the unique channel has index $1$; the displayed family $A_d$ is used only for $d\ge2$.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 3, Theorem 1.2

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

/-- Theorem 1.2, PDF p.3 (ceiling confirmed on p.21): universal bound AND sharp
example in every positive dimension. At d=1 the unique channel has index 1;
the separate explicit A_d family is used only for d>=2. -/
theorem theorem1_2 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi) :
    (EventuallyClassicalScrambling Phi →
      quantumTime Phi ≤ classicalTime Phi ∧ classicalTime Phi ≤ (d ^ 2 : ℕ)) ∧
    (∃ Psi : Dynamics d, IsChannel Psi ∧
      classicalTime Psi = (scramblingBound d : WithTop ℕ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
