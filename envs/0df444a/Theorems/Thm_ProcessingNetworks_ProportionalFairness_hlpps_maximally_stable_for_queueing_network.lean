-- Prove2me | Theorems.Thm_ProcessingNetworks_ProportionalFairness_hlpps_maximally_stable_for_queueing_network
-- name    : ProcessingNetworks.ProportionalFairness.hlpps_maximally_stable_for_queueing_network
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T19:36:57.561827+00:00
-- url     : https://prove2.me/theorems/71d6b832-4437-4b21-9c29-7056d9340cea
-- title:
--   Corollary 10.18 — HLPPS is maximally stable for a queueing network (milestone)
-- statement:
--   **Corollary 10.18.** The HLPPS control policy is stable for any subcritical queueing network.
--   Thus HLPPS is maximally stable for a queueing network.
--
--   The partition of Section 10.4 specializes, for a queueing network, to one demand group per
--   server (`grp := server`), under which the reduced allocation set becomes the box $\prod_k
--   [0,b_k]$ (Eq. 10.78) and the aggregate PF allocation function is simply $\tilde\psi \equiv b$:
--   each server's full capacity, divided among its classes in proportion to job counts. This is
--   exactly HLPPS (Section 4.6), so Corollary 10.16 applies directly.
--
--   **Formalization note.** Stated exactly as Corollary 10.16, for the HLPPS specialization
--   (`HLPPSFluidStable`, Definition 10.3's PF fluid model with `grp := server` and
--   $\tilde{\mathcal A} := \prod_k [0,b_k]$): an abstract policy type with `PolicyStable`, the
--   HLPPS policy `hlpps`, `hfluid` (Theorem 6.2 with Proposition 4.4's identification of the HLPPS
--   network with its head-of-line model) and `hnecessary` (Theorem 5.2 with Proposition 5.1: every
--   $\lambda$ in the stability region satisfies the standard load condition
--   $\rho_k = \sum_{i : \mathrm{server}(i) = k} \alpha_i m_i < b_k$). The content established is
--   Theorem 10.5 for this specialization throughout the subcritical region.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 207, Corollary 10.18

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_BWSAndQueueing
import Definitions.Def_ProcessingNetworks_ProportionalFairness_MaximalStability

namespace ProcessingNetworks.ProportionalFairness

/-- Corollary 10.18, Dai & Harrison p. 207 (PDF p. 223): the HLPPS control policy is stable for
any subcritical queueing network, and hence HLPPS is maximally stable for a queueing network.
HLPPS coincides with PF control specialized to `grp := server` and the box
`Ã := ∏_k [0, b_k]` (Eq. 10.78, `HLPPSFluidStable`), so the statement is Corollary 10.16 for that
specialization, with the same network-level facts as explicit hypotheses: `hfluid` (Theorem 6.2
together with Proposition 4.4's identification of the HLPPS network with its head-of-line model:
if the HLPPS fluid model at `lam` is stable then `hlpps` is a stable policy at `lam`) and
`hnecessary` (Theorem 5.2 with Proposition 5.1: every `lam` in the stability region is
nonnegative and satisfies the standard load condition `ρ < b`, `ρ_k = ∑_{i : server i = k} αᵢ mᵢ`,
with `alpha lam` the total-arrival-rate vector (2.38) at `lam`). -/
theorem hlpps_maximally_stable_for_queueing_network
    {I K : ℕ} {Policy : Type*} (m : Fin I → ℝ) (hm : ∀ i, 0 < m i)
    (P : Matrix (Fin I) (Fin I) ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_rowsum : ∀ i, ∑ j, P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (P ^ n) i j) Filter.atTop (nhds 0))
    (server : Fin I → Fin K) (b : Fin K → ℝ) (hb : ∀ k, 0 < b k)
    (alpha : (Fin I → ℝ) → (Fin I → ℝ))
    (halpha : ∀ lam, IsTotalArrivalRates
      (⟨lam, m, hm, P, server, {y : Fin K → ℝ | ∀ k, 0 ≤ y k ∧ y k ≤ b k}⟩ :
        PFUnitaryNetworkData I K) (alpha lam))
    (PolicyStable : Policy → (Fin I → ℝ) → Prop) (hlpps : Policy)
    (hfluid : ∀ lam : Fin I → ℝ,
      HLPPSFluidStable (⟨lam, m, hm, P, server, b, hb⟩ : QueueingNetworkDataHL I K) →
        PolicyStable hlpps lam)
    (hnecessary : ∀ lam ∈ StabilityRegion PolicyStable, (∀ i, 0 ≤ lam i) ∧
      ∀ k, groupAggregate server (fun i => alpha lam i * m i) k < b k) :
    IsMaximallyStable PolicyStable hlpps := by sorry

end ProcessingNetworks.ProportionalFairness
