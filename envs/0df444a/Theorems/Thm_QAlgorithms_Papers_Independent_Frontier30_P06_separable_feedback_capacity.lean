-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P06_separable_feedback_capacity
-- name    : QAlgorithms.Papers.Independent.Frontier30.P06.separable_feedback_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:24:01.702967+00:00
-- url     : https://prove2.me/theorems/ae8481ad-0038-44c1-89b1-23b1222004fd
-- title:
--   No capacity gain across separable feedback cuts
-- statement:
--   Let $N$ be a fixed completely positive trace-preserving channel between positive finite-dimensional systems. There is no initial shared resource; the only side communication is noiseless classical communication from receiver to sender. Rates are measured in bits per physical forward-channel use, with uniform-message average decoding error tending to zero.
--
--   Allow arbitrary block lengths and arbitrary entanglement inside each block. At every feedback step between blocks require the actual average total state to be separable across the cut between the receiver together with an untouched classical message reference, and every retained sender register, both before and after that feedback operation. Write $C_{\mathrm{sep,FB}}(N)$ for the supremum of achievable rates in this class, and $C(N)$ for the unassisted operational classical capacity. Then
--
--   $$
--   C_{\mathrm{sep,FB}}(N)\le C(N).
--   $$
--
--   This is a converse for feedback across separable cuts. It makes no additivity assumption about the single-block Holevo quantity.
-- source:
--   On Feedback and the Classical Capacity of a Noisy Quantum Channel, arXiv:quant-ph/0305176v1, PDF p. 4, III.B

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Frontier30.P06

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Backward tensorAction)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

/-- PDF p.4, III.B (announced p.1): classical feedback across non-entangled cuts
cannot increase operational C. Arbitrary entanglement within blocks is allowed;
no single-use Holevo additivity assumption is imposed on a general channel. -/
theorem separable_feedback_capacity (N : Backward) (hN : ChannelValid N) :
    separableFeedbackCapacity N ≤ unassistedCapacity N := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P06

end
