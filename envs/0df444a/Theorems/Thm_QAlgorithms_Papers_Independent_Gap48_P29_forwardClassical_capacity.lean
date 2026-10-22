-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P29_forwardClassical_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P29.forwardClassical_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:22:15.712202+00:00
-- url     : https://prove2.me/theorems/6f2d3a27-ca02-4aa2-8f28-f827117133fa
-- title:
--   Forward classical communication does not increase capacity
-- statement:
--   Let $\mathcal N$ be a completely positive trace-preserving channel with nonzero finite-dimensional input and output spaces. A code consists of trace-preserving encoders, $n$ independent uses of $\mathcal N$, and trace-preserving decoders, with no prior entanglement or feedback. Write $Q_e(\mathcal N)$ for the supremum of entropy rates of reliably transmitted QAEP sources, and $Q_s(\mathcal N)$ for the supremum of reliably transmitted subspace rates, measured using minimum squared pure-state fidelity. Source entropy rate and subspace rate use the limsup per channel use, with entropy and logarithms in bits. Permit an arbitrary finite number of forward classical messages at every block length: the encoder is a CP trace-nonincreasing instrument whose branches sum to a trace-preserving map, and the decoder uses a trace-preserving map depending on the message. Define reliability by the sum of unrenormalized branch entanglement fidelities, and let $Q_e^{(fc)}$ be the supremum of reliably transmitted QAEP-source entropy rates. Then
--
--   $$Q_e^{(fc)}(\mathcal N)=Q_e(\mathcal N).$$
--
--   This concerns asymptotically reliable transmission and permits no feedback or prior entanglement.
-- source:
--   On Quantum Fidelities and Channel Capacities, arXiv:quant-ph/9809010v1, PDF p. 11, Theorem 5, Eqs.(97)–(102)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder Topology

open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)

open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

/-- PDF p.11, Theorem 5: unrestricted finite forward classical messages do not
increase asymptotically reliable entanglement capacity. -/
theorem forwardClassical_capacity {c o : ℕ} (hc : 0 < c) (ho : 0 < o)
    (N : Superop (Fin c) (Fin o)) (hN : IsChannel N) : qeForward N = qe N := by sorry

end QAlgorithms.Papers.Independent.Gap48.P29

end
