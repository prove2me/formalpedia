-- Prove2me | Theorems.Thm_ProcessingNetworks_FeedforwardStability_generalized_jackson_stable
-- name    : ProcessingNetworks.FeedforwardStability.generalized_jackson_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T18:07:03.273723+00:00
-- url     : https://prove2.me/theorems/1e983193-a61d-4deb-a537-18435078bb33
-- title:
--   Corollary 8.19 — generalized Jackson networks stable under non-idling FCFS (milestone)
-- statement:
--   A **generalized Jackson network** is a queueing network with a one-to-one correspondence
--   between job classes and server pools ($I=J=K$, each pool serving exactly one class).
--
--   **Corollary 8.19.** For a generalized Jackson network, if the standard load condition
--   $\rho < b$ holds, the fluid model is stable under the non-idling FCFS policy.
--
--   This follows because HLSPS reduces to non-idling FCFS for such networks: since each pool
--   serves only one class, $\gamma_i = \alpha_i m_i / \rho_{p(i)} = 1$ automatically (a pool's
--   entire load comes from its single class), so HLSPS's "split capacity in proportions $\gamma$"
--   becomes "give the one class all the capacity whenever it is non-empty" — exactly non-idling.
--
--   **Formalization note.** The structural hypothesis is `Function.Bijective dat.p` (a
--   one-to-one correspondence between the `I` classes and `K` pools, matching "$I=J=K$"), and the
--   conclusion reuses `NonIdlingFluidStable` directly — the same object Theorem 8.14 concludes
--   stability of — rather than restating a separate "FCFS fluid model," since the book's own
--   remark identifies the two for this network class exactly.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 148, Corollary 8.19

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_FeedforwardStability_NonIdling

namespace ProcessingNetworks.FeedforwardStability

/-- Corollary 8.19, Dai & Harrison p. 148 (PDF p. 164): a generalized Jackson network is a
queueing network with a one-to-one correspondence between classes and server pools
(`dat.p` bijective, so `I = K` and each pool serves exactly one class — HLSPS then reduces to
non-idling FCFS, since `γ ≡ 1`). If the standard load condition `ρ < b` holds, the fluid model is
stable under the non-idling FCFS policy. -/
theorem generalized_jackson_stable
    {I K : ℕ} (dat : QueueingNetworkData I K) (hgj : Function.Bijective dat.p)
    (Q : Matrix (Fin I) (Fin I) ℝ) (hQ : IsRoutingInverse dat.P Q)
    (hload : ∀ k : Fin K, workloadOperator dat Q dat.lam k < dat.b k) :
    NonIdlingFluidStable dat := by sorry

end ProcessingNetworks.FeedforwardStability
