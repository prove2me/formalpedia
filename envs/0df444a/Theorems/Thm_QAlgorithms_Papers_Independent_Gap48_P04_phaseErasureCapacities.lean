-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P04_phaseErasureCapacities
-- name    : QAlgorithms.Papers.Independent.Gap48.P04.phaseErasureCapacities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:55:51.535168+00:00
-- url     : https://prove2.me/theorems/9f981ae7-b241-4201-9335-71d8ed77b2ba
-- title:
--   Exact capacities of the flagged phase-erasure channel
-- statement:
--   For a finite-dimensional memoryless quantum channel, write $Q$ for unassisted quantum transmission capacity, $Q_2$ for quantum transmission capacity with free two-way classical communication, and $C$ for unassisted classical capacity. Quantum rates are in qubits per forward use and classical rates are in bits per forward use. Encoders and decoders are arbitrary CPTP operations, with no efficiency restriction. Quantum reliability is squared pure-state fidelity uniformly over every normalized unknown logical input. Classical reliability is worst-message decoding error. A code is chosen before its input; for every rate below capacity and every positive error tolerance a positive block length and a code of strictly greater rate exist. Independent uses act on arbitrary entangled blocks. Two-way protocols have arbitrary finite adaptive classical rounds and finite quantum memories, with no initial shared entanglement. For $0\le\epsilon\le1$, define the flagged phase-erasure channel by $\Phi_\epsilon(\rho)=(1-\epsilon)\rho\otimes|0\rangle\langle0|+\epsilon\Delta_Z(\rho)\otimes|1\rangle\langle1|$, where $\Delta_Z(\rho)=(\rho+Z\rho Z^\dagger)/2$ and $Z=\operatorname{diag}(1,-1)$. The second output qubit is a receiver flag. Then
--
--   $$Q(\Phi_\epsilon)=Q_2(\Phi_\epsilon)=1-\epsilon,\qquad C(\Phi_\epsilon)=1.$$
--
--   The flag distinguishes intact transmissions from dephased ones, while computational-basis classical information remains perfectly readable even at $\epsilon=1$.
-- source:
--   Capacities of Quantum Erasure Channels, arXiv:quant-ph/9701015v2, PDF p. 3, Following Eq. (3)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P04

namespace QAlgorithms.Papers.Independent.Gap48.P04

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation mixed)

/-- Bennett--DiVincenzo--Smolin, PDF p.3, following Eq.(3): the receiver's
phase-erasure flag is retained. At p=1 quantum capacity vanishes and C=1. -/
theorem phaseErasureCapacities (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniformQuantumCapacity (phaseErasure p) = ENNReal.ofReal (1-p) ∧
    adaptiveQuantumCapacity (phaseErasure p) = ENNReal.ofReal (1-p) ∧
    worstMessageCapacity (phaseErasure p) = 1 := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P04
