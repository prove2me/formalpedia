-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P04_erasureCapacities
-- name    : QAlgorithms.Papers.Independent.Gap48.P04.erasureCapacities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:54:55.156766+00:00
-- url     : https://prove2.me/theorems/99408a7a-15e2-4244-a8b1-3d24c91b7227
-- title:
--   Exact capacities of the qubit quantum erasure channel
-- statement:
--   For a finite-dimensional memoryless quantum channel, write $Q$ for unassisted quantum transmission capacity, $Q_2$ for quantum transmission capacity with free two-way classical communication, and $C$ for unassisted classical capacity. Quantum rates are in qubits per forward use and classical rates are in bits per forward use. Encoders and decoders are arbitrary CPTP operations, with no efficiency restriction. Quantum reliability is squared pure-state fidelity uniformly over every normalized unknown logical input. Classical reliability is worst-message decoding error. A code is chosen before its input; for every rate below capacity and every positive error tolerance a positive block length and a code of strictly greater rate exist. Independent uses act on arbitrary entangled blocks. Two-way protocols have arbitrary finite adaptive classical rounds and finite quantum memories, with no initial shared entanglement. Let $0\le\epsilon\le1$. The qubit erasure channel sends a density matrix $\rho$ to $(1-\epsilon)\rho\oplus\epsilon\operatorname{Tr}(\rho)$; its last, one-dimensional output block is the orthogonal erasure flag. Its capacities are
--
--   $$Q=\max\{0,1-2\epsilon\},\qquad Q_2=C=1-\epsilon.$$
--
--   This gives all three operational capacities, including the endpoints and the threshold $\epsilon=1/2$.
-- source:
--   Capacities of Quantum Erasure Channels, arXiv:quant-ph/9701015v2, PDF p. 2, Eq. (2)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P04

namespace QAlgorithms.Papers.Independent.Gap48.P04

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation mixed)

/-- Bennett--DiVincenzo--Smolin, PDF p.2, Eq.(2): all three operational
capacities of the qubit erasure channel, including p=0,1/2,1. -/
theorem erasureCapacities (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let N := QAlgorithms.Papers.Independent.Dependency50.P09.erasureFin 2 p
    uniformQuantumCapacity N = ENNReal.ofReal (max 0 (1-2*p)) ∧
    adaptiveQuantumCapacity N = ENNReal.ofReal (1-p) ∧
    worstMessageCapacity N = ENNReal.ofReal (1-p) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P04
