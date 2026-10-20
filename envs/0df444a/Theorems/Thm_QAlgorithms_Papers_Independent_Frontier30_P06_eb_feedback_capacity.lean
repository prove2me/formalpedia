-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P06_eb_feedback_capacity
-- name    : QAlgorithms.Papers.Independent.Frontier30.P06.eb_feedback_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:26:29.604328+00:00
-- url     : https://prove2.me/theorems/fc3cdea9-6292-4c4e-ba1c-dd643b8e3e53
-- title:
--   Classical feedback does not increase forward entanglement-breaking capacity
-- statement:
--   Let $N$ be a positive finite-dimensional entanglement-breaking channel: it is completely positive and trace-preserving, and applying it to one side of any density operator with any finite reference yields a separable state. Let $C(N)$ be its unassisted operational classical capacity and $C_{\mathrm{FB}}(N)$ its capacity with arbitrary noiseless classical receiver-to-sender feedback. There is no prior shared entanglement; the code may use arbitrary entangled inputs and changing local quantum memories. Using uniform-message average error tending to zero and bits per physical forward use,
--
--   $$
--   C_{\mathrm{FB}}(N)=C(N).
--   $$
--
--   This equality concerns an entanglement-breaking forward channel. It is not a statement about allowing entanglement-breaking backward quantum channels.
-- source:
--   On Feedback and the Classical Capacity of a Noisy Quantum Channel, arXiv:quant-ph/0305176v1, PDF p. 4, III.C; IV

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Frontier30.P06

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Backward tensorAction)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

/-- PDF pp.1,4, III.C and IV: classical feedback cannot increase the capacity
of a forward entanglement-breaking channel, even with entangled inputs.
The accepted rectangular EB predicate quantifies over every finite reference.
Unrestricted feedback is operationalCapacity with the always-true restriction;
it uses uniform-message average POVM error, distinct from P09.feedbackCapacity. -/
theorem eb_feedback_capacity (N : Backward) (hEB : N.IsEB) :
    operationalCapacity N (fun _ => True) = unassistedCapacity N := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P06

end
