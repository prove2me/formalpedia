-- Prove2me | Theorems.Thm_TradeCredit_Terms_proposition3_two_part_low_cash
-- name    : TradeCredit.Terms.proposition3_two_part_low_cash
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T09:40:40.900031+00:00
-- url     : https://prove2.me/theorems/6a8356e8-f1f8-47be-80fd-4dcf54034e0a
-- title:
--   Proposition 3 (item 2), p. 15 — with α_t > 0 and small cash K, every optimal contract has θ_b* > 0 (two-part terms)
-- statement:
--   Let the demand density $f$ satisfy the standing assumptions of §3 (continuous, positive on $[0,\infty)$, zero on $(-\infty,0)$, total mass one, increasing failure rate), let $0<c<1$, $\alpha_b\in[0,1]$, and suppose trade-credit default is **costly**: $0<\alpha_t\le 1$.
--
--   Then there is a cash threshold $\bar K>0$ such that for every retailer cash level $K\in(0,\bar K)$, **every** optimal trade credit contract $(\theta_b^*,\theta_t^*)$ — a maximizer of the supplier's profit (8) over the threshold domain $\Theta$ — has a strictly positive bank-loan default threshold:
--   $$\theta_b^*>0 .$$
--
--   Since $\theta_b=(1+r_b)B$ and $d_t^*=1-\hat F_b(\theta_b^*)$, this says that for low cash the supplier offers **two-part terms** ($d_t^*>0$) and the retailer takes a bank loan. This is the core of item 2 of Proposition 3; the paper's proof (p. 38) reduces "two-part terms are optimal" to exactly the claim $\theta_b^*>0$ ("it is equivalent to show that $\theta_b^*>0$"), argued from the first-order conditions (44)–(45) for small $K$.
--
--   The objects $\Theta$, $\Pi_s$, $Q$, $C$, $\hat F_b$ and `IsOptimalContract` are those of the mission's model definition `TradeCredit_Terms_Model`. The threshold $\bar K$ may depend on $f,c,\alpha_b,\alpha_t$ but not on the contract; the statement does not assert that an optimal contract exists.
-- source:
--   Yang & Birge, Trade Credit, Risk Sharing, and Inventory Financing Portfolios, Management Science 64(8) (2018), accepted manuscript (LBS Research Online eprint 801), p. 15, Proposition 3 item 2; proof p. 38 (eqs. (44)-(45))

import Mathlib
import Definitions.Def_TradeCredit_Terms_Model

namespace TradeCredit.Terms

theorem proposition3_two_part_low_cash (f : ℝ → ℝ) (hf : DemandModel f)
    (c αb αt : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hαb0 : 0 ≤ αb) (hαb1 : αb ≤ 1)
    (hαt0 : 0 < αt) (hαt1 : αt ≤ 1) :
    ∃ Khigh : ℝ, 0 < Khigh ∧ ∀ K : ℝ, 0 < K → K < Khigh →
      ∀ θb θt : ℝ, IsOptimalContract f c αb αt K θb θt → 0 < θb := by sorry

end TradeCredit.Terms
