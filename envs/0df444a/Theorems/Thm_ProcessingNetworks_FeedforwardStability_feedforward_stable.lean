-- Prove2me | Theorems.Thm_ProcessingNetworks_FeedforwardStability_feedforward_stable
-- name    : ProcessingNetworks.FeedforwardStability.feedforward_stable
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T18:05:23.63499+00:00
-- url     : https://prove2.me/theorems/dc9c8263-fab6-4229-9673-25ccd025738f
-- title:
--   Theorem 8.14 — feedforward network stable under any non-idling policy (milestone)
-- statement:
--   **Theorem 8.14.** Consider a feedforward queueing network. If the standard load condition
--   $\rho < b$ holds, then the fluid model under *any* non-idling policy is stable, and thus, by
--   Theorem 6.2, the feedforward queueing network is stable under any non-idling policy.
--
--   This is the chapter's first capstone: a purely structural condition on the routing matrix
--   (feedforward) plus a purely numerical one (subcriticality) suffices for stability, with no
--   restriction at all on which non-idling policy is used. The proof constructs a piecewise-linear
--   Lyapunov function $H(z) = \max_k \delta_k W_k(z)$ from a carefully chosen sequence of weights
--   $\delta_k$ exploiting the routing matrix's block-triangular structure, then applies Lemma 8.5
--   via Lemma 8.10 (derivative of a maximum) and Lemma 8.15 (the workload derivative identity).
--
--   **Formalization note.** The standard load condition $\rho < b$ is stated component-wise as
--   `∀ k, workloadOperator dat Q dat.lam k < dat.b k`, matching (5.1) via $\rho = W(\lambda)$
--   (Eq. 8.25). The conclusion is `NonIdlingFluidStable dat`, with no reference to *which*
--   non-idling policy is used — matching "stable under any non-idling policy" exactly, since
--   `IsNonIdlingSolution` quantifies over every solution satisfying the non-idling condition, not
--   a fixed one.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 145, Theorem 8.14

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_Feedforward
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_FeedforwardStability_NonIdling

namespace ProcessingNetworks.FeedforwardStability

/-- Theorem 8.14, Dai & Harrison p. 145 (PDF p. 161): consider a feedforward queueing network. If
the standard load condition `ρ < b` (Eq. 5.1, `ρ := W(λ)`) holds, then the fluid model under any
non-idling policy is stable (and hence, by Theorem 6.2, the network itself is stable under any
non-idling policy). -/
theorem feedforward_stable
    {I K : ℕ} (dat : QueueingNetworkData I K) (hff : IsFeedforward dat)
    (Q : Matrix (Fin I) (Fin I) ℝ) (hQ : IsRoutingInverse dat.P Q)
    (hload : ∀ k : Fin K, workloadOperator dat Q dat.lam k < dat.b k) :
    NonIdlingFluidStable dat := by sorry

end ProcessingNetworks.FeedforwardStability
