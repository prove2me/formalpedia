-- Prove2me | Theorems.Thm_RideHailing_Central_proposition_1_scarce
-- name    : RideHailing.Central.proposition_1_scarce
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:26.884259+00:00
-- url     : https://prove2.me/theorems/d8d6e4c3-1cce-4b56-ba00-1ae6c7242591
-- title:
--   Proposition 1(1), p. 8 — with scarce capacity n ≤ n^C_1 every selected optimal allocation has s̄ = n, r = 0, q = 0
-- statement:
--   Consider the two-location ride-hailing model under centralized control, with the standing assumptions of the mission (Assumptions 1–3 and the model conventions). Let $n^C_1=\bar S-(\Lambda_{21}-\Lambda_{12})t_{21}$ as in (17).
--
--   **Proposition 1(1) (scarce capacity).** Let $0\le n\le n^C_1$. Then the two-step selection is nonempty: there is an allocation in $\mathcal C^*_C(n)$, the revenue-maximizing allocations of capacity $n$, that maximizes the per-driver profit $\pi(s,r,n)$ among them. Every such selected allocation has
--   $$\bar s=n,\qquad r_{12}=r_{21}=0,\qquad q_1=q_2=0,$$
--   so all drivers serve riders.
--
--   This is the first zone of the parametric solution of the platform's capacity-allocation problem (14); it determines the per-driver profit $\pi_C(n)=\bar\gamma p-c$ in zone 1 of (18).
--
--   **Formalization Note** "The following optimal allocation" is read as the two-step selection of §2.5 (the per-driver-profit-maximizing elements of $\mathcal C^*_C(n)$). Only the totals $\bar s$, and the components of $r$ and $q$, are pinned, as on the page; the vector $s$ is not unique. Proposition 1 does not mention $N$, so $n$ ranges over $[0,n^C_1]$ without the bound $n\le N$.
-- source:
--   Afèche, Liu, Maglaras, Ride-Hailing Networks with Strategic Drivers: The Impact of Platform Control Capabilities on Performance, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2023.1221, p. 8, Proposition 1(1)

import Mathlib
import Definitions.Def_RideHailing_Central_Setting

namespace RideHailing.Central
theorem proposition_1_scarce (M : Model) (hM : M.Standing) (n : ℝ) (hn0 : 0 ≤ n)
    (hn : n ≤ M.nC1) :
    (M.SelC n).Nonempty ∧
      ∀ x ∈ M.SelC n, x.sbar = n ∧ x.r12 = 0 ∧ x.r21 = 0 ∧ x.q1 = 0 ∧ x.q2 = 0 := by sorry
end RideHailing.Central
