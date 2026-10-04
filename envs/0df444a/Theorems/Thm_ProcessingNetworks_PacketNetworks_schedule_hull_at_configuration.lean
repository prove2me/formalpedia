-- Prove2me | Theorems.Thm_ProcessingNetworks_PacketNetworks_schedule_hull_at_configuration
-- name    : ProcessingNetworks.PacketNetworks.schedule_hull_at_configuration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T19:48:17.460088+00:00
-- url     : https://prove2.me/theorems/7e2b96c0-61ae-4f09-adc9-49fb0fac4042
-- title:
--   Proposition 12.6 — the convex hull of Sc is the A-polytope (milestone)
-- statement:
--   **Proposition 12.6.** For each $c\in C$, $\langle S_c\rangle = \{x\in\mathbb R^J_+ :
--   Ax\le c\}$.
--
--   The book's proof constructs, for $x$ in the polytope, an explicit product-form distribution
--   over $S_c$ (independently randomizing each link's segment) whose mean is $x$ — genuinely
--   non-trivial, not a formal triviality of the hull operator.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 231, Proposition 12.6

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations
import Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion

namespace ProcessingNetworks.PacketNetworks

/-- Proposition 12.6, Dai & Harrison p. 231 (PDF p. 247): for each configuration `c`, `⟨Sc⟩ =
{x ∈ ℝ^J_+ : Ax ≤ c}` — the convex hull of the (integer) schedule set at `c` is exactly the real
polytope cut out by the link-usage matrix, no more and no less. -/
theorem schedule_hull_at_configuration
    {J K : ℕ} (cfg : LinkConfigData J K) (c : Fin K → ℕ) (Sc : Finset (Fin J → ℕ))
    (hSc : IsScheduleSetAt cfg c Sc) :
    hullFinset Sc = {x : Fin J → ℝ | (∀ j, 0 ≤ x j) ∧ ∀ k, (cfg.A.mulVec x) k ≤ (c k : ℝ)} := by sorry

end ProcessingNetworks.PacketNetworks
