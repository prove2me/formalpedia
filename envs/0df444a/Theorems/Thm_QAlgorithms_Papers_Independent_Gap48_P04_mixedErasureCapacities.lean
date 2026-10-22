-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P04_mixedErasureCapacities
-- name    : QAlgorithms.Papers.Independent.Gap48.P04.mixedErasureCapacities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:56:55.702311+00:00
-- url     : https://prove2.me/theorems/6ab5ef85-e17c-4d76-afb5-ff9b6cf1f146
-- title:
--   Capacities of the mixed flagged erasure and phase-erasure channel
-- statement:
--   For a finite-dimensional memoryless quantum channel, write $Q$ for unassisted quantum transmission capacity, $Q_2$ for quantum transmission capacity with free two-way classical communication, and $C$ for unassisted classical capacity. Quantum rates are in qubits per forward use and classical rates are in bits per forward use. Encoders and decoders are arbitrary CPTP operations, with no efficiency restriction. Quantum reliability is squared pure-state fidelity uniformly over every normalized unknown logical input. Classical reliability is worst-message decoding error. A code is chosen before its input; for every rate below capacity and every positive error tolerance a positive block length and a code of strictly greater rate exist. Independent uses act on arbitrary entangled blocks. Two-way protocols have arbitrary finite adaptive classical rounds and finite quantum memories, with no initial shared entanglement. Let $\epsilon,\delta\ge0$ and $\delta+\epsilon\le1$. The mutually exclusive events of full erasure, phase erasure, and undisturbed transmission have unconditional probabilities $\epsilon$, $\delta$, and $1-\delta-\epsilon$. Retaining all receiver flags, the channel on an operator $X$ is $(1-\delta-\epsilon)X\oplus\delta\Delta_Z(X)\oplus\epsilon\operatorname{Tr}(X)$, with output block dimensions $2+2+1$. Its capacities are
--
--   $$Q=\max\{0,1-\delta-2\epsilon\},\qquad Q_2=1-\delta-\epsilon,\qquad C=1-\epsilon.$$
--
--   This includes the entire closed probability simplex, rather than only the equal-probability slice depicted in the figure.
-- source:
--   Capacities of Quantum Erasure Channels, arXiv:quant-ph/9701015v2, PDF p. 3, Eq. (4)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P04

namespace QAlgorithms.Papers.Independent.Gap48.P04

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation mixed)

/-- Bennett--DiVincenzo--Smolin, PDF p.3, Eq.(4): mutually exclusive full and
phase erasures, with their distinct flags and the entire closed probability simplex. -/
theorem mixedErasureCapacities (p delta : ℝ) (hp : 0 ≤ p) (hd : 0 ≤ delta)
    (hsum : delta+p ≤ 1) :
    uniformQuantumCapacity (mixedErasure p delta) = ENNReal.ofReal (max 0 (1-delta-2*p)) ∧
    adaptiveQuantumCapacity (mixedErasure p delta) = ENNReal.ofReal (1-delta-p) ∧
    worstMessageCapacity (mixedErasure p delta) = ENNReal.ofReal (1-p) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P04
