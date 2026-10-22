-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P04_erasureCoherentInformation
-- name    : QAlgorithms.Papers.Independent.Gap48.P04.erasureCoherentInformation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:58:36.231149+00:00
-- url     : https://prove2.me/theorems/ebfdd1ee-c205-4952-b542-a942bc676519
-- title:
--   Maximum one-use coherent information of the qubit erasure channel
-- statement:
--   For a finite-dimensional memoryless quantum channel, write $Q$ for unassisted quantum transmission capacity, $Q_2$ for quantum transmission capacity with free two-way classical communication, and $C$ for unassisted classical capacity. Quantum rates are in qubits per forward use and classical rates are in bits per forward use. Encoders and decoders are arbitrary CPTP operations, with no efficiency restriction. Quantum reliability is squared pure-state fidelity uniformly over every normalized unknown logical input. Classical reliability is worst-message decoding error. A code is chosen before its input; for every rate below capacity and every positive error tolerance a positive block length and a code of strictly greater rate exist. Independent uses act on arbitrary entangled blocks. Two-way protocols have arbitrary finite adaptive classical rounds and finite quantum memories, with no initial shared entanglement. For $0\le\epsilon\le1$, let $\mathcal E_\epsilon$ be the qubit erasure channel with a one-dimensional orthogonal erasure output. For an input density matrix $\rho$, write $I_c(\rho,\mathcal E_\epsilon)=S(\mathcal E_\epsilon(\rho))-S((\mathrm{id}\otimes\mathcal E_\epsilon)(|\psi_\rho\rangle\langle\psi_\rho|))$, where $|\psi_\rho\rangle$ is a purification and $S$ is von Neumann entropy in bits. This signed quantity has an attained maximum satisfying
--
--   $$\max_\rho I_c(\rho,\mathcal E_\epsilon)=Q(\mathcal E_\epsilon)=\max\{0,1-2\epsilon\}.$$
--
--   For $\epsilon<1/2$, the maximally mixed input $I_2/2$ attains the maximum. For $\epsilon\ge1/2$, the fixed pure input $|0\rangle\langle0|$ attains it. These are specified maximizing inputs, without any uniqueness claim.
--
--   This connects a one-use entropic optimum with the independently defined operational quantum capacity for this channel.
-- source:
--   Capacities of Quantum Erasure Channels, arXiv:quant-ph/9701015v2, PDF p. 3, Unnumbered coherent-information paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P04

namespace QAlgorithms.Papers.Independent.Gap48.P04

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation mixed)

/-- Bennett--DiVincenzo--Smolin, PDF p.3: maximum single-use coherent information
and its attaining inputs. 'Random qubit state' means I/2. The pure witness remains
valid at p=1/2; no assertion that all inputs have zero information for p>1/2. -/
theorem erasureCoherentInformation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let N := QAlgorithms.Papers.Independent.Dependency50.P09.erasureFin 2 p
    let value := max 0 (1-2*p)
    singleUseInformation N = value ∧
    uniformQuantumCapacity N = ENNReal.ofReal (singleUseInformation N) ∧
    IsGreatest {v | ∃ rho : Op (Fin 2), IsDensityMatrix rho ∧
      v = coherentInformation N rho} value ∧
    (p < 1/2 → coherentInformation N (mixed (Fin 2)) = value) ∧
    (1/2 ≤ p → coherentInformation N (pureDensity (ket (0 : Fin 2))) = value) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P04
