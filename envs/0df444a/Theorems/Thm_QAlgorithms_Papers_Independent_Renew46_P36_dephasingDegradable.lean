-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_dephasingDegradable
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.dephasingDegradable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:11:48.807994+00:00
-- url     : https://prove2.me/theorems/093d98e1-1a08-46e9-b877-4c703ee62483
-- title:
--   Appendix B: dephasing identities and explicit degrader
-- statement:
--   Let $A'$ and $E$ be finite nonzero complex registers, with a fixed orthonormal basis $\{|i\rangle\}$ of $A'$, and normalized environment vectors $|\phi_i\rangle\in E$, which need not be orthogonal. Define the isometry $U|i\rangle=|i\rangle|\phi_i\rangle$, the generalized dephasing channel $\mathcal N=\operatorname{Tr}_E\circ U(\cdot)U^\dagger$, its same-dilation complement $\mathcal N^c=\operatorname{Tr}_{A'}\circ U(\cdot)U^\dagger$, and complete dephasing $\Delta(X)=\sum_i|i\rangle\langle i|X|i\rangle\langle i|$. On all operators,
--
--   $$
--   \Delta\circ\mathcal N=\mathcal N\circ\Delta=\Delta,\qquad
--   \mathcal N^c\circ\Delta=\mathcal N^c,\qquad
--   \mathcal N^c\circ\mathcal N=\mathcal N^c.
--   $$
--
--   The map $T=\mathcal N^c$, now acting on the receiver register with the same basis, is CPTP and is an explicit degrading map. Thus $\mathcal N$ is degradable and its operational quantum capacity equals its single-letter maximum coherent information in bits. The statement includes a density matrix attaining this value.
--
--   These identities retain the physical degrading witness and equality of maps, rather than merely their values on one state.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 13, Appendix B: dephasing identities and explicit degrader

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}

variable [Fintype A] [Fintype B] [Fintype E]

variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- Appendix B, PDF p.13: all dephasing identities on ALL operators, together
with the explicit physical degrader T=N^c and the attained quantum-capacity maximum.
Environment vectors are normalized but need not be orthogonal. -/
theorem dephasingDegradable
    [Nonempty A] [Nonempty E] (env : A → EuclideanSpace ℂ E)
    (henv : ∀ a, ‖env a‖ = 1) :
    let N := generalizedDephasing env
    let Nc := complementaryChannel (dephasingIsometry env)
    diagonalPart ∘ N = diagonalPart ∧ N ∘ diagonalPart = diagonalPart ∧
    Nc ∘ diagonalPart = Nc ∧ IsChannel Nc ∧ Nc ∘ N = Nc ∧
    IsDegradable (dephasingIsometry env) ∧
    quantumCapacity N = maximumCoherentInformation (dephasingIsometry env) ∧
    ∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
      quantumCapacity N = vnEntropy (N rho) - vnEntropy (Nc rho) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
