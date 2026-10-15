-- Prove2me | Theorems.Thm_RideHailing_Central_proposition_1_moderate
-- name    : RideHailing.Central.proposition_1_moderate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:35.688689+00:00
-- url     : https://prove2.me/theorems/3bec25aa-fb50-4c00-a419-7ac9d0b12ad8
-- title:
--   Proposition 1(2), p. 8 — with moderate capacity n^C_1 < n ≤ n^C_2 selected allocations have s̄ + r12 = n, r12 = t12/(t12+t21)(n − n^C_1), r21 = 0, q = 0
-- statement:
--   Consider the two-location ride-hailing model under centralized control, with the standing assumptions of the mission, and the thresholds $n^C_1,n^C_2$ of (17).
--
--   **Proposition 1(2) (moderate capacity).** Let $n^C_1<n\le n^C_2$. Then the two-step selection (the elements of $\mathcal C^*_C(n)$ that maximize the per-driver profit) is nonempty, and every selected allocation satisfies
--   $$\bar s+r_{12}=n,\qquad r_{12}=\frac{t_{12}}{t_{12}+t_{21}}\,(n-n^C_1),\qquad r_{21}=0,\qquad q_1=q_2=0.$$
--   Drivers serve riders or reposition empty from the low-demand location 1 to the high-demand location 2.
--
--   In this zone the extra capacity beyond $n^C_1$ serves excess cross-location demand from 2 to 1, which requires empty repositioning back; the formula gives the share of that capacity spent repositioning, and determines zone 2 of (18).
--
--   **Formalization Note** The page's $t_{12}/(t_{12}+t_{21})(n-n^C_1)$ is read as the product $\frac{t_{12}}{t_{12}+t_{21}}\cdot(n-n^C_1)$, as typeset. The selection is the two-step selection of §2.5.
-- source:
--   Afèche, Liu, Maglaras, Ride-Hailing Networks with Strategic Drivers: The Impact of Platform Control Capabilities on Performance, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2023.1221, p. 8, Proposition 1(2)

import Mathlib
import Definitions.Def_RideHailing_Central_Setting

namespace RideHailing.Central
theorem proposition_1_moderate (M : Model) (hM : M.Standing) (n : ℝ) (hn1 : M.nC1 < n)
    (hn2 : n ≤ M.nC2) :
    (M.SelC n).Nonempty ∧
      ∀ x ∈ M.SelC n, x.sbar + x.r12 = n ∧
        x.r12 = M.t12 / (M.t12 + M.t21) * (n - M.nC1) ∧ x.r21 = 0 ∧ x.q1 = 0 ∧ x.q2 = 0 := by sorry
end RideHailing.Central
