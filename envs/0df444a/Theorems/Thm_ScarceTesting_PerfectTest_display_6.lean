-- Prove2me | Theorems.Thm_ScarceTesting_PerfectTest_display_6
-- name    : ScarceTesting.PerfectTest.display_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:28.068845+00:00
-- url     : https://prove2.me/theorems/149bf93d-5042-41e0-a8a7-8e72fcd37f6d
-- title:
--   Display (6), p. 11 — the demand for a (φ,σ)-test is F(t_H) − F(t_L), so the availability is min{1, κ/(F(t_H) − F(t_L))}
-- statement:
--   Throughout, $0<c<1$ is the cost-to-benefit ratio of acting (seeking treatment), and a $(\varphi,\sigma)$-test has false positive rate $\varphi$ and true positive rate $\sigma$ with $0\le\varphi\le\sigma\le1$, $\sigma>0$ and $\varphi<1$. The prior density $f$ is a nonnegative integrable function on $[0,1]$ with total mass $1$, and $F(x)=\int_0^x f$. Let $0<\kappa<1$ be the mass of available test kits. The demand $D(\varphi,\sigma)$ — the $f$-mass of agents with positive value of the test — equals
--   $$D(\varphi,\sigma)=F(t_H)-F(t_L),$$
--   and consequently the availability under uniformly random allocation is
--   $$\min\Big\{1,\frac{\kappa}{D(\varphi,\sigma)}\Big\}=A(t_L,t_H)=\min\Big\{1,\frac{\kappa}{F(t_H)-F(t_L)}\Big\}.$$
--
--   This expresses the congestion created by a test entirely through its two thresholds.
--
--   **Formalization Note** The conditions $\sigma>0$ and $\varphi<1$ keep the denominators of $t_L$ and $t_H$ positive (Lean evaluates $0/0$ as $0$); they exclude only the degenerate $(0,0)$- and $(1,1)$-tests. The availability is $1$ when the demand does not exceed $\kappa$, including zero demand.
-- source:
--   Drakopoulos & Randhawa, Why Perfect Tests May Not Be Worth Waiting For: Information as a Commodity, SSRN 3565245 (version of January 13, 2021), display (6) and the availability A(t_L,t_H), p. 11

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

namespace ScarceTesting.PerfectTest

/-- Display (6) and the availability, p. 11: the demand for a `(φ,σ)`-test is
`D(φ,σ) = F(t_H) − F(t_L)`, so the availability is `A(t_L,t_H) = min{1, κ/(F(t_H) − F(t_L))}`. -/
theorem display_6 (f : ℝ → ℝ) (c κ φ σ : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 ≤ φ) (hφσ : φ ≤ σ) (hσ1 : σ ≤ 1)
    (hσ0 : 0 < σ) (hφ1 : φ < 1)
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hf : IsPriorDensity f) :
    demand f c φ σ = cdf f (tH c φ σ) - cdf f (tL c φ σ) ∧
    availability κ (demand f c φ σ) = availThr f κ (tL c φ σ) (tH c φ σ) := by sorry

end ScarceTesting.PerfectTest
