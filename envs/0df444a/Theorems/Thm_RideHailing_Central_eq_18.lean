-- Prove2me | Theorems.Thm_RideHailing_Central_eq_18
-- name    : RideHailing.Central.eq_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:35.309992+00:00
-- url     : https://prove2.me/theorems/e1f5ad9b-12fa-4110-ab13-6bd5c00c8d40
-- title:
--   (18), p. 8 — closed form of the regime-C per-driver profit π_C(n) in the three capacity zones
-- statement:
--   Consider the two-location ride-hailing model under centralized control, with the standing assumptions of the mission. Let $\pi_C(n)$ be the per-driver profit of the two-step selected allocation of capacity $n$, i.e. the largest value of $\pi(s,r,n)=((\bar\gamma p-c)\bar s-c\bar r)/n$ over the revenue-maximizing allocations $\mathcal C^*_C(n)$.
--
--   **Display (18).** For every $n>0$,
--   $$\pi_C(n)=\begin{cases}\bar\gamma p-c, & n\le n^C_1,\\[4pt] \dfrac1n\,\bar\gamma p\Big(n^C_1+(n-n^C_1)\dfrac{t_{21}}{t_{12}+t_{21}}\Big)-c, & n^C_1<n\le n^C_2,\\[8pt] \dfrac1n\big(\bar\gamma p\bar S-c\,n^C_2\big), & n>n^C_2.\end{cases}$$
--
--   The closed form reflects the drivers' utilization profile: in zone 1 they serve riders all the time, in zone 2 they drive all the time but serve riders only a fraction of it, and in zone 3 they also queue. It is the input to Corollary 1(i).
--
--   **Formalization Note** $\pi_C$ is defined through the allocation problem, not by this formula, so the statement is a genuine consequence of Proposition 1. The value at $n=0$ is excluded because (12d) divides by $n$.
-- source:
--   Afèche, Liu, Maglaras, Ride-Hailing Networks with Strategic Drivers: The Impact of Platform Control Capabilities on Performance, Manufacturing & Service Operations Management, Articles in Advance (2023), doi:10.1287/msom.2023.1221, p. 8, §3, (18)

import Mathlib
import Definitions.Def_RideHailing_Central_Setting

namespace RideHailing.Central
theorem eq_18 (M : Model) (hM : M.Standing) (n : ℝ) (hn : 0 < n) :
    (n ≤ M.nC1 → M.piC n = M.gbar * M.p - M.c) ∧
    (M.nC1 < n → n ≤ M.nC2 →
      M.piC n = 1 / n * (M.gbar * M.p) * (M.nC1 + (n - M.nC1) * (M.t21 / (M.t12 + M.t21))) - M.c) ∧
    (M.nC2 < n → M.piC n = 1 / n * (M.gbar * M.p * M.Sbar - M.c * M.nC2)) := by sorry
end RideHailing.Central
