-- Prove2me | Theorems.Thm_SennottDP_ContinuousTime_mm1_serve_avg_cost
-- name    : SennottDP.ContinuousTime.mm1_serve_avg_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T11:17:33.49026+00:00
-- url     : https://prove2.me/theorems/3b0747a0-a83c-41a9-997d-13a8ee690616
-- title:
--   Proposition 10.4.1 — the average cost of serving the M/M/1 queue at a constant rate a > λ
-- statement:
--   Consider the M/M/1 queue with service rate control of Example 10.2.1, with arrival rate $\lambda>0$, a finite set of positive service rates, nonnegative service cost rates $c(a)$, and linear holding cost rate $H(i)=Hi$ with $H>0$. Let $a$ be one of the service rates with $\lambda<a$, let $d(a)$ be the policy that always serves at rate $a$, and let $\rho_a=\lambda/a$. Then, from every initial state,
--
--   $$J^\Psi_{d(a)}=\rho_a\,c(a)+\frac{H\rho_a}{1-\rho_a}.$$
--
--   The first term is the service cost rate times the fraction of time the server is busy, the second the expected holding cost; the value serves as a benchmark for the optimal policy computed in Section 10.4.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 250, Proposition 10.4.1, eq. (10.28); p. 249 (H(i) = Hi with H > 0)

import Mathlib
import Definitions.Def_SennottDP_ContinuousTime_MM1

open scoped ENNReal

namespace SennottDP.ContinuousTime

/-- Proposition 10.4.1 (p. 250). -/
theorem mm1_serve_avg_cost (lam H a : ℝ) (rates : Finset ℝ) (c : ℝ → ℝ) (hlam : 0 < lam)
    (hrates : ∀ b ∈ rates, 0 < b) (hc : ∀ b ∈ rates, 0 ≤ c b) (hH : 0 < H)
    (ha : a ∈ rates) (hla : lam < a) :
    ∀ i, CTMDC.avgCost (mm1Serve lam rates c (fun k => H * k) a ha) i =
      ENNReal.ofReal (lam / a * c a + H * (lam / a) / (1 - lam / a)) := by sorry

end SennottDP.ContinuousTime
