-- Prove2me | Theorems.Thm_RobustSPA_IID_SPA_isDSIC
-- name    : RobustSPA.IID.SPA_isDSIC
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-24T09:06:35.060682+00:00
-- url     : https://prove2.me/theorems/5ef914ea-a8ad-4b33-b251-fd28a96e7f96
-- title:
--   p. 16, §3.2 — for any reserve distribution Φ, the second-price auction SPA(Φ) belongs to the DSIC class 𝓜
-- statement:
--   Let $n\ge 0$ and let $\rho$ be any probability law on $\mathbb R$ (the law of the random reserve $q$, with CDF $\Phi$). The second-price auction with random reserve $\mathrm{SPA}(\Phi)$ allocates the item to the highest bidder $i$ (ties broken in favour of the lowest index) with probability $\Phi(v_i)=\rho((-\infty,v_i])$ and charges the winner
--   $$p_i(\mathbf v)=\mathbb E_{q\sim\rho}\big[\max(v^{(2)},q)\,\mathbf 1(v_i\ge q)\big],$$
--   where $v^{(2)}$ is the second-highest bid; losers get nothing and pay nothing. Then
--   $$\mathrm{SPA}(\Phi)\in\mathcal M ,$$
--   i.e. on the type cube $[0,1]^n$ the mechanism is individually rational, dominant-strategy incentive compatible, allocates at most one unit with probabilities in $[0,1]$, and has measurable allocation and payment rules with bounded payments.
--
--   This is the membership fact used throughout the paper (Theorem 1, Propositions 2, 4, 5): every minimax argument evaluates $\sup_F R_n(\mathrm{SPA}(\Phi),F)$ as one of the mechanisms in the infimum defining the minimax regret.
--
--   **Formalization Note.** $\mathcal M$ is `Mechanism.IsDSIC` of the shared `RobustSPA.IID.Setting` (IR, IC, AC on $[0,1]^n$, allocations in $[0,1]$, measurability, bounded payments). The same statement over the identical `RobustSPA.AllDist` setting is `RobustSPA.AllDist.SPA_isDSIC`.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. 16 (§3.2, paragraph before Proposition 1: "for any $\Phi$, SPA($\Phi$) $\in \mathcal M$: the second-price auction with random reserve mechanism is DSIC"); see also p. 13

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting

namespace RobustSPA.IID

open MeasureTheory

theorem SPA_isDSIC (n : ℕ) (ρ : ProbabilityMeasure ℝ) :
    (SPA (n := n) (ρ : Measure ℝ)).IsDSIC := by sorry

end RobustSPA.IID
