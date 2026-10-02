-- Prove2me | Theorems.Thm_ProcessingNetworks_FeedforwardStability_workload_derivative_nonidling
-- name    : ProcessingNetworks.FeedforwardStability.workload_derivative_nonidling
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T18:06:06.533483+00:00
-- url     : https://prove2.me/theorems/279f47fa-4fe3-4cc6-b0c6-4723c134e65c
-- title:
--   Lemma 8.15 — the workload derivative identity (milestone)
-- statement:
--   **Lemma 8.15.** Consider a queueing network operating under a non-idling policy. If a fluid
--   model solution $(D,F,T,Z)$ is differentiable at $t > 0$, then for each station $k$,
--   $\sum_{i\in I(k)} Z_i(t) > 0$ implies
--   $$
--   \frac{d}{dt} W_k(Z(t)) = \rho_k - b_k.
--   $$
--
--   This isolates the drift of the workload process at a busy station: workload builds up at
--   rate $\rho_k$ (the station's load) and drains at rate $b_k$ (its capacity) whenever the
--   station has work, giving a net drift of $\rho_k - b_k$ — negative exactly under the standard
--   load condition. It is the calculational core both Theorem 8.14 and Theorem 8.18's proofs
--   invoke.
--
--   **Formalization note.** "$\dot W_k(Z(t)) = \rho_k - b_k$" is stated as a universally
--   quantified implication over witnessing derivatives (`∀ d, HasDerivAt ... d t → d = ...`),
--   consistent with mission V's convention, rather than an existential differentiability claim.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 145, Lemma 8.15

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_FeedforwardStability_NonIdling

namespace ProcessingNetworks.FeedforwardStability

/-- Lemma 8.15, Dai & Harrison p. 145 (PDF p. 161): consider a queueing network operating under a
non-idling policy. For each station `k`, whenever `∑_{i∈I(k)} Zᵢ(t) > 0`,
`d/dt Wₖ(Z(t)) = ρₖ - bₖ`, where `ρₖ := Wₖ(λ)`. -/
theorem workload_derivative_nonidling
    {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (hQ : IsRoutingInverse dat.P Q)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hni : IsNonIdlingSolution dat Dh Fh Th Zh)
    (k : Fin K) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ poolBuffers dat k, Zh t i) :
    ∀ d : ℝ, HasDerivAt (fun s => workloadOperator dat Q (Zh s) k) d t →
      d = workloadOperator dat Q dat.lam k - dat.b k := by sorry

end ProcessingNetworks.FeedforwardStability
