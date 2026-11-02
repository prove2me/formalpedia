-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_local_cptp_simulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.local_cptp_simulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:04:21.640903+00:00
-- url     : https://prove2.me/theorems/02675b1a-8fad-44e3-ad03-df73e3272db4
-- title:
--   Simulation of local CPTP protocols by local unitaries
-- statement:
--   Let $P$ be a finite two-party protocol on separate finite classical input sets. Its $k$ alternating messages have fixed senders and fixed transmitted wires; each local operation is a complex-linear CPTP map controlled only by its owner's input. Its normalized initial work state is independent of both inputs, and its final output measurement belongs to the announcing player. Let $c(P)$ be the number of transmitted qubits.
--
--   There is a protocol $Q$ using local unitaries and additional private blank qubits, with the same starting player, number of messages and announcing player, such that
--   $$
--   c(Q)\le c(P),\qquad
--   \Pr_Q[o\mid x,y]=\Pr_P[o\mid x,y]\quad\text{for every }x,y,o.
--   $$
--
--   The initial state of $Q$ is exactly the original state embedded on ownership-preserving wires, tensor additional zero qubits. Thus the simulation introduces no stronger prior entanglement or input-dependent advice. This expresses equality of full output distributions, not merely preservation of one success probability.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 6, Unnumbered model simulation paragraph

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Unnumbered simulation claim, PDF p.6: arbitrary local CPTP operations can be purified
using only additional private blank qubits, preserving every output probability, rounds and cost. -/
theorem local_cptp_simulation {X Y O : Type} [Fintype X] [Fintype Y] [Fintype O]
    (P : ChannelProtocol X Y O) (start : Party) (k : ℕ) (hP : P.valid start k) :
    ∃ Q : QuantumProtocol X Y O, Q.valid start k ∧ BlankExtension P Q ∧
      Q.cost ≤ P.cost ∧ Q.outputParty = P.outputParty ∧
      ∀ x y o, Q.probability x y o = P.probability x y o := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
