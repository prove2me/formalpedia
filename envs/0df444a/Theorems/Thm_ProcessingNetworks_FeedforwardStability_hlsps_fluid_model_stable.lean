-- Prove2me | Theorems.Thm_ProcessingNetworks_FeedforwardStability_hlsps_fluid_model_stable
-- name    : ProcessingNetworks.FeedforwardStability.hlsps_fluid_model_stable
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T18:06:40.22842+00:00
-- url     : https://prove2.me/theorems/8a396c0d-96a7-476e-a822-adce7ebff97b
-- title:
--   Theorem 8.18 — HLSPS control is stable under the standard load condition (goal)
-- statement:
--   This is the goal theorem of the mission. Unlike Theorem 8.14, it makes no feedforward
--   assumption at all — it applies to *any* queueing network — but is specific to one particular
--   control policy (HLSPS) rather than an arbitrary non-idling one.
--
--   **Theorem 8.18.** Consider a queueing network subject to relaxed control, and let $\gamma$ be
--   the proportion vector of (8.30). If the standard load condition $\rho < b$ holds, then the
--   fluid model for the HLSPS control policy with proportion vector $\gamma$ is stable, and thus,
--   by Theorem 6.2, the queueing network is stable under that HLSPS policy.
--
--   The proof (via Lemma 8.20) uses a *linear* Lyapunov function $f(t) = e'(I-P')^{-1}Z(t)$ (the
--   total number of services still required anywhere in the network), rather than the
--   piecewise-linear one Theorem 8.14 needs — the price of dropping the feedforward assumption is
--   paid for by specializing to one policy whose fixed capacity-splitting proportions make a
--   linear potential work for any routing structure.
--
--   **Formalization note.** The standard load condition is stated explicitly via
--   $\rho_k = W_k(\lambda)$; the model-data positivity conventions ($m > 0$, $\lambda \ge 0$, $b > 0$,
--   $P$ substochastic and transient) are carried by `QueueingNetworkData` itself. Every class is
--   assumed to have a positive total arrival rate, $\alpha_i > 0$ (`hα_pos`): the proportions
--   $\gamma_i = \alpha_i m_i / \rho_k$ of (8.30) are only defined when $\rho_k > 0$, and the book's
--   proof takes $\varepsilon := \min_{k,\, j \in I(k)} (b_k/\rho_k - 1)\alpha_j$, which is positive
--   only when every $\alpha_j > 0$ — a class with $\alpha_j = 0$ would receive the proportion
--   $\gamma_j = 0$, never be served, and any initial fluid in it would remain forever, so the
--   theorem is false without this (implicit in the book) assumption. No additional structural
--   hypothesis (feedforward, generalized-Jackson) is imposed, matching the theorem's own "any
--   queueing network" scope exactly.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 148, Theorem 8.18

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_FeedforwardStability_HLSPS

namespace ProcessingNetworks.FeedforwardStability

/-- Theorem 8.18, Dai & Harrison p. 148 (PDF p. 164) — the goal theorem of this mission: consider
a queueing network subject to relaxed control, with `γ` the proportion vector of (8.30). If the
standard load condition `ρ < b` holds, then the fluid model corresponding to the HLSPS control
policy with proportion vector `γ` is stable, and thus, by Theorem 6.2, the queueing network is
also stable under that HLSPS control policy. Every class is assumed to have a positive total
arrival rate `αᵢ > 0` (`hα_pos`): the proportions `γᵢ = αᵢmᵢ/ρₖ` of (8.30) are only defined for
`ρₖ > 0`, and the proof's `ε := min (bₖ/ρₖ - 1) αⱼ` is positive only when every `αⱼ > 0` (a class
with `αⱼ = 0` would receive the proportion `γⱼ = 0` and never be served). -/
theorem hlsps_fluid_model_stable
    {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (hQ : IsRoutingInverse dat.P Q)
    (hα_pos : ∀ i : Fin I, 0 < totalArrivalRates dat Q i)
    (hload : ∀ k : Fin K, workloadOperator dat Q dat.lam k < dat.b k) :
    HLSPSFluidStable dat Q := by sorry

end ProcessingNetworks.FeedforwardStability
