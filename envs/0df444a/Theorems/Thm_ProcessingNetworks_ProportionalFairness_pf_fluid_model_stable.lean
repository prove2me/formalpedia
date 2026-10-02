-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_pf_fluid_model_stable
-- name    : ProcessingNetworks.ProportionalFairness.pf_fluid_model_stable
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:22:46.539116+00:00
-- url     : https://prove2.me/theorems/58d98c8c-b3d5-4ed5-9681-254db7dc8204
-- title:
--   Theorem 10.5 — fluid stability of the PF control policy (goal)
-- statement:
--   This is the goal theorem of the mission.
--
--   **Theorem 10.5.** If the load condition (10.37) holds, the PF fluid model is stable.
--
--   The book itself flags this proof as "long and intricate": its Lyapunov function (the entropy
--   function $\varphi$ of Eq. 10.38) is *not* absolutely continuous, unlike essentially every
--   other Lyapunov function used elsewhere in the book, so the extinction criterion it invokes
--   must be the Dini-derivative-based Lemma 8.11 (mission V), not the simpler Lipschitz-based
--   Lemmas 8.5/8.6.
--
--   **Formalization note.** The hypothesis is exactly (10.37) (`hload`, via `IsTotalArrivalRates`
--   for `α`), matching the book's own "If (10.37) holds..." phrasing, under the standing assumptions
--   of the chapter: $\tilde{\mathcal A}$ has the properties assumed of an allocation set
--   (`hdom`), and the unitary network's data satisfy $\lambda \ge 0$ and $P$ substochastic and
--   transient (Section 10.4), so that $\alpha$ is the network's total-arrival-rate vector. The
--   conclusion `PFFluidStable` is Definition 6.3 (mission III) specialized to the PF fluid model.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 196, Theorem 10.5

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_FluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_Aggregation

namespace ProcessingNetworks.ProportionalFairness

/-- Theorem 10.5, Dai & Harrison p. 196 (PDF p. 212) — the goal theorem of this mission: if the
load condition (10.37) holds (`γ < a` for some `a ∈ Ã`), the PF fluid model is stable. The book's
own proof is "long and intricate," using an entropy Lyapunov function that is not absolutely
continuous — the deepest single theorem of the chapter. -/
theorem pf_fluid_model_stable
    {I L : ℕ} (dat : PFUnitaryNetworkData I L)
    (hdom : IsPFDomain dat.TildeAllocSet) (hlam : ∀ i, 0 ≤ dat.lam i)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (dat.P ^ n) i j) Filter.atTop (nhds 0))
    (alpha : Fin I → ℝ) (halpha : IsTotalArrivalRates dat alpha)
    (hload : ∃ a ∈ dat.TildeAllocSet, ∀ ℓ, groupAggregate dat.grp (fun i => alpha i * dat.m i) ℓ < a ℓ) :
    PFFluidStable dat := by sorry

end ProcessingNetworks.ProportionalFairness
