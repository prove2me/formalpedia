-- Prove2me | Theorems.Thm_ProcessingNetworks_GlobalStability_ring_globally_stable
-- name    : ProcessingNetworks.GlobalStability.ring_globally_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T18:14:08.515363+00:00
-- url     : https://prove2.me/theorems/cb042132-9982-49a7-9a5b-2882e4391e7c
-- title:
--   Theorem 8.24 — unidirectional ring network is globally stable (milestone)
-- statement:
--   **Theorem 8.24.** If a unidirectional ring network satisfies the standard load condition
--   $\rho < e$, then its fluid model is globally stable — with *no* restriction at all on the
--   arrival-rate vector $\lambda$ or mean-service-time vector $m$ beyond subcriticality, unlike
--   the re-entrant line of Theorem 8.25.
--
--   The proof builds a piecewise-linear Lyapunov function from the per-station "arrived minus
--   served" processes $G_k(t) := \sum_{(\ell,j):p(\ell,j)=k} Z^+_{\ell j}(t)$, using the ring's
--   cyclic structure to show that whenever the maximum $h = \max_k G_k$ is attained only at
--   stations with no immediate predecessor contributing fluid, the *next* station downstream must
--   have positive content, driving the drift below $-\varepsilon$.
--
--   **Formalization note.** The ring's structural hypothesis is `IsUnidirectionalRing`, which
--   encodes the same content as the book's per-type route description via a flat successor
--   function (see that item's own formalization note); the data satisfy $\lambda \ge 0$ and $m > 0$
--   as for every queueing network of Section 2.6 (`hlam`, `hm`); the conclusion
--   `FluidModelGloballyStable` is Definition 8.23 applied to the network `dat`.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 152, Theorem 8.24

import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_GlobalStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_GlobalStability_UnidirectionalRing
import Definitions.Def_ProcessingNetworks_GlobalStability_NonIdlingFluidModel

namespace ProcessingNetworks.GlobalStability

/-- Theorem 8.24, Dai & Harrison p. 152 (PDF p. 168): if a unidirectional ring network satisfies
the standard load condition `ρ < e` (`ρ := W(λ)`, `e` the vector of ones), then its fluid model
is globally stable. The arrival rates are nonnegative and the mean service times positive, as
for every queueing network of Section 2.6. -/
theorem ring_globally_stable
    {I K : ℕ} (dat : QueueingNetworkData I K) (succ : Fin I → Option (Fin I))
    (hring : IsUnidirectionalRing dat succ)
    (hlam : ∀ i, 0 ≤ dat.lam i) (hm : ∀ i, 0 < dat.m i)
    (Q : Matrix (Fin I) (Fin I) ℝ) (hQ : IsRoutingInverse dat.P Q)
    (hload : ∀ k : Fin K, workloadOperator dat Q dat.lam k < dat.b k) :
    FluidModelGloballyStable dat := by sorry

end ProcessingNetworks.GlobalStability
