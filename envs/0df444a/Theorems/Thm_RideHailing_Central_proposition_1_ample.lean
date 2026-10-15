-- Prove2me | Theorems.Thm_RideHailing_Central_proposition_1_ample
-- name    : RideHailing.Central.proposition_1_ample
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:34.962975+00:00
-- url     : https://prove2.me/theorems/fbf7c500-2207-49cf-b28f-7bb8df8870cf
-- title:
--   Proposition 1(3), p. 8 — with ample capacity n > n^C_2 selected allocations have s̄ = S̄, r12 = n^C_2 − S̄, r21 = 0, q̄ = n − n^C_2
-- statement:
--   Consider the two-location ride-hailing model under centralized control, with the standing assumptions of the mission, and the thresholds $n^C_1,n^C_2$ of (17).
--
--   **Proposition 1(3) (ample capacity).** Let $n>n^C_2$. Then the two-step selection is nonempty, and every selected allocation satisfies
--   $$\bar s=\bar S,\qquad r_{12}=n^C_2-\bar S,\qquad r_{21}=0,\qquad \bar q=n-n^C_2.$$
--   Drivers serve all riders, reposition from the low- to the high-demand location, or wait in queue.
--
--   This zone shows that under centralized control drivers idle in queue only once all demand is served; it determines zone 3 of (18).
--
--   **Formalization Note** Platform optimality alone fixes $\bar s=\bar S$ but not $r_{21}$; the value $r_{21}=0$ comes from the second step of the selection (maximizing per-driver profit), which relies on the driving cost $c$ being positive, one of the mission's standing conventions. Only the total $\bar q$ is pinned, as on the page.
-- source:
--   Afèche, Liu, Maglaras, Ride-Hailing Networks with Strategic Drivers: The Impact of Platform Control Capabilities on Performance, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2023.1221, p. 8, Proposition 1(3)

import Mathlib
import Definitions.Def_RideHailing_Central_Setting

namespace RideHailing.Central
theorem proposition_1_ample (M : Model) (hM : M.Standing) (n : ℝ) (hn : M.nC2 < n) :
    (M.SelC n).Nonempty ∧
      ∀ x ∈ M.SelC n, x.sbar = M.Sbar ∧ x.r12 = M.nC2 - M.Sbar ∧ x.r21 = 0 ∧
        x.qbar = n - M.nC2 := by sorry
end RideHailing.Central
