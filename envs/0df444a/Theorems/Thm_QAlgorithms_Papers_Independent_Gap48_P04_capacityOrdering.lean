-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P04_capacityOrdering
-- name    : QAlgorithms.Papers.Independent.Gap48.P04.capacityOrdering
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:00:09.34512+00:00
-- url     : https://prove2.me/theorems/26b5c2ee-fc30-40a5-9802-31c1166d0e9e
-- title:
--   General ordering of the unassisted quantum capacity
-- statement:
--   For a finite-dimensional memoryless quantum channel, write $Q$ for unassisted quantum transmission capacity, $Q_2$ for quantum transmission capacity with free two-way classical communication, and $C$ for unassisted classical capacity. Quantum rates are in qubits per forward use and classical rates are in bits per forward use. Encoders and decoders are arbitrary CPTP operations, with no efficiency restriction. Quantum reliability is squared pure-state fidelity uniformly over every normalized unknown logical input. Classical reliability is worst-message decoding error. A code is chosen before its input; for every rate below capacity and every positive error tolerance a positive block length and a code of strictly greater rate exist. Independent uses act on arbitrary entangled blocks. Two-way protocols have arbitrary finite adaptive classical rounds and finite quantum memories, with no initial shared entanglement. For every CPTP channel $\mathcal N$ from a nonzero finite-dimensional input register to a nonzero finite-dimensional output register,
--
--   $$Q(\mathcal N)\le Q_2(\mathcal N),\qquad Q(\mathcal N)\le C(\mathcal N).$$
--
--   This places unassisted quantum transmission below both assisted quantum transmission and unassisted classical communication. It asserts no ordering between $Q_2$ and $C$.
-- source:
--   Capacities of Quantum Erasure Channels, arXiv:quant-ph/9701015v2, PDF p. 2, Unnumbered capacity-ordering observation

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P04

namespace QAlgorithms.Papers.Independent.Gap48.P04

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation mixed)

/-- Bennett--DiVincenzo--Smolin, PDF p.2: Q <= Q2 and Q <= C for every
finite-dimensional CPTP channel. No ordering between Q2 and C is asserted. -/
theorem capacityOrdering (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (N : Superop (Fin d) (Fin e)) (hN : IsChannel N) :
    uniformQuantumCapacity N ≤ adaptiveQuantumCapacity N ∧ uniformQuantumCapacity N ≤ worstMessageCapacity N := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P04
