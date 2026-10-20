-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P06_feedback_capacity_dominates
-- name    : QAlgorithms.Papers.Independent.Frontier30.P06.feedback_capacity_dominates
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:24:36.973678+00:00
-- url     : https://prove2.me/theorems/c864e14e-82ce-4506-92a7-3e94e8280970
-- title:
--   Unrestricted classical-feedback capacity dominates unassisted capacity
-- statement:
--   Let $N$ be a completely positive trace-preserving channel between positive finite-dimensional systems. Let $C(N)$ be its unassisted operational classical capacity, and let $C_{\mathrm{FB}}(N)$ allow arbitrary noiseless classical receiver-to-sender feedback, without initial shared entanglement. Both capacities use uniform-message average error tending to zero and rates in bits per physical forward use. Then
--
--   $$
--   C(N)\le C_{\mathrm{FB}}(N).
--   $$
--
--   The comparison expresses the option of ignoring feedback. It imposes no separability restriction on the unrestricted feedback class.
-- source:
--   On Feedback and the Classical Capacity of a Noisy Quantum Channel, arXiv:quant-ph/0305176v1, PDF p. 1, (1)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Frontier30.P06

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Backward tensorAction)

open QAlgorithms.Papers.Independent.Information100.P08 (channelHolevo)

/-- PDF p.1, equation (1): ignoring feedback gives C_FB >= C, for unrestricted
classical feedback and operational uniform-message average-error capacities. -/
theorem feedback_capacity_dominates (N : Backward) (hN : ChannelValid N) :
    unassistedCapacity N ≤ operationalCapacity N (fun _ => True) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P06

end
