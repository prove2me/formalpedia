-- Prove2me | Theorems.Thm_ProcessingNetworks_PacketNetworks_schedule_hull
-- name    : ProcessingNetworks.PacketNetworks.schedule_hull
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T19:48:46.767354+00:00
-- url     : https://prove2.me/theorems/6d45173d-2291-47e2-9fc0-41c079216474
-- title:
--   Corollary 12.7 — the convex hull of S via the configuration hull (milestone)
-- statement:
--   **Corollary 12.7.** $\langle S\rangle = \{x\in\mathbb R^J_+ : Ax\le\hat c\text{ for some
--   }\hat c\in\langle C\rangle\}$.
--
--   This is the union-over-configurations lift of Proposition 12.6, and is exactly the reduced,
--   group-level characterization Theorem 12.8's proof and Proposition 12.9 both build on.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 232, Corollary 12.7

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion

namespace ProcessingNetworks.PacketNetworks

/-- Corollary 12.7, Dai & Harrison p. 232 (PDF p. 248): `⟨S⟩ = {x ∈ ℝ^J_+ : Ax ≤ ĉ for some ĉ ∈
⟨C⟩}` — lifting Proposition 12.6 from a single configuration `c` to the full configuration mix
`ĉ` ranging over `⟨C⟩`. -/
theorem schedule_hull
    {J K : ℕ} (cfg : LinkConfigData J K) (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S) :
    hullFinset S =
      {x : Fin J → ℝ | (∀ j, 0 ≤ x j) ∧ ∃ chat ∈ hullFinset cfg.C,
        ∀ k, (cfg.A.mulVec x) k ≤ chat k} := by sorry

end ProcessingNetworks.PacketNetworks
