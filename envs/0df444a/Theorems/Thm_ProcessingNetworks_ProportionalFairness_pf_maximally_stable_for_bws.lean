-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_pf_maximally_stable_for_bws
-- name    : ProcessingNetworks.ProportionalFairness.pf_maximally_stable_for_bws
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T19:36:08.890329+00:00
-- url     : https://prove2.me/theorems/9d9c50e8-2cbd-42f0-9e2e-7665ae91529a
-- title:
--   Corollary 10.17 — PF is maximally stable for a BWS network (milestone)
-- statement:
--   **Corollary 10.17.** If the standard load condition $\rho < b$ is satisfied, then a BWS
--   network is stable under PF control, and otherwise it is not stable under any control policy.
--   In this sense, proportional fairness is maximally stable for a BWS network.
--
--   The book's proof chains Proposition 4.4 (a processor-sharing model is stable iff its EHL model
--   is), the EHL-model translation of Section 4.4, Proposition 5.1 (standard load condition iff
--   subcriticality), Theorem 5.2 (subcriticality is necessary for stability under any policy), and
--   Corollary 10.16 (this chunk's own goal).
--
--   **Formalization note.** The three facts structurally outside this chunk's own apparatus
--   (Proposition 4.4 with the Section 4.4 model translation as `hpf`, Proposition 5.1 in
--   group-level form as `hload_iff`, and Theorem 5.2 as `hnecessary`) are explicit hypotheses
--   rather than re-derived, per this series' convention for content belonging to other chapters;
--   the reduced allocation set of the EHL representation is an allocation set in the sense of
--   Section 10.1 (`hdom`), as Theorem 10.5 requires. The genuine content proved here is deriving
--   the corollary's two-sided conclusion from these together with Theorem 10.5. "Not stable under
--   any control policy" is stated with a universal quantifier over an arbitrary `Policy` type,
--   matching Corollary 5.6/10.16's own maximal-stability pattern (mission II) and this chunk's own
--   `BRIEF.md` pitfall note.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 206-207, Corollary 10.17

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore
import Definitions.Def_ProcessingNetworks_ProportionalFairness_BWSAndQueueing

namespace ProcessingNetworks.ProportionalFairness

/-- Corollary 10.17, Dai & Harrison p. 206 (PDF p. 222): if the standard load condition `ρ < b`
holds, a BWS network is stable under PF control; otherwise it is not stable under any control
policy. The book's own proof chains three facts outside this chunk's own apparatus — Proposition
4.4 (a processor-sharing model is stable iff its EHL model is stable) together with the model
translation of Section 4.4 (`hpf`: PF-stability of the BWS network is equivalent to fluid
stability of its EHL-model unitary-network representation, `grp`/`TildeAllocSet`), Proposition 5.1
(standard load condition iff subcriticality, in the group-level form `hload_iff`), and Theorem 5.2
(subcriticality is necessary for any stable policy to exist, `hnecessary`) — each packaged as an
explicit hypothesis, per this series' convention for content structurally outside a chunk's own
scope; the genuine content proved here is deriving the corollary's two-way conclusion from these
together with Corollary 10.16 (`pf_control_maximally_stable`, this chunk's own goal item). -/
theorem pf_maximally_stable_for_bws
    {I K L : ℕ} {Policy : Type*} (PolicyStable : Policy → BWSNetworkData I K → Prop)
    (pf : Policy) (grp : Fin I → Fin L) (TildeAllocSet : Set (Fin L → ℝ))
    (hdom : IsPFDomain TildeAllocSet)
    (hpf : ∀ dat : BWSNetworkData I K,
      PolicyStable pf dat ↔
        PFFluidStable (⟨dat.lam, dat.m, dat.hm, 0, grp, TildeAllocSet⟩ : PFUnitaryNetworkData I L))
    (hload_iff : ∀ dat : BWSNetworkData I K,
      BWSLoadCondition dat ↔
        ∃ a ∈ TildeAllocSet, ∀ ℓ, groupAggregate grp (fun i => dat.lam i * dat.m i) ℓ < a ℓ)
    (hnecessary : ∀ dat : BWSNetworkData I K, ¬ BWSLoadCondition dat → ∀ p, ¬ PolicyStable p dat)
    (dat : BWSNetworkData I K) :
    (BWSLoadCondition dat → PolicyStable pf dat) ∧
    (¬ BWSLoadCondition dat → ∀ p, ¬ PolicyStable p dat) := by sorry

end ProcessingNetworks.ProportionalFairness
