-- Prove2me | Theorems.Thm_TradeCredit_Terms_proposition3_optimal_terms
-- name    : TradeCredit.Terms.proposition3_optimal_terms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:59.861966+00:00
-- url     : https://prove2.me/theorems/e350aa7c-c1c4-4c97-8192-294d232a3f3e
-- title:
--   Proposition 3, p. 15 — the optimal contract always uses trade credit; net terms if α_t = 0 or K is large, two-part terms if α_t > 0 and K is small
-- statement:
--   Let the demand density $f$ satisfy the standing assumptions of §3 (continuous, positive on $[0,\infty)$, IFR), and let the unit cost satisfy $0<c<1$ and the deadweight cost proportions satisfy $\alpha_b,\alpha_t\in[0,1]$. For retailer cash $K>0$, an **optimal trade credit contract** is a pair of thresholds $(\theta_b^*,\theta_t^*)$ that maximizes the supplier's profit (8) over the threshold domain $\Theta$. Here $\theta_b$ is the bank-loan default threshold, $\theta_t$ the trade-credit default threshold, and the early-payment discount is $d_t^*=1-\hat F_b(\theta_b^*)$. Let $M^*=g^{-1}(1)\bar F(g^{-1}(1))$.
--
--   Then:
--   1. **Trade credit is always used.** For every $K>0$, every optimal contract with $\theta_t^*>0$ (the retailer uses external financing) has $\theta_b^*<\theta_t^*$ (the retailer uses trade credit).
--   2. **Net terms when trade-credit default is costless.** If $\alpha_t=0$, then for every $K>0$ every optimal contract has $\theta_b^*=0$ and $d_t^*=0$.
--   3. **Net terms when cash is high.** There is $\underline K<M^*$ such that for every $K\in[\underline K,M^*)$ with $K>0$, every optimal contract has $\theta_b^*=0$ and $d_t^*=0$.
--   4. **Two-part terms when cash is low.** If $\alpha_t>0$, there is $\bar K>0$ such that for every $K\in(0,\bar K)$, every optimal contract has
--   $$0<\theta_b^*<\theta_t^*\quad\text{and}\quad d_t^*>0 .$$
--
--   In words: when the supplier designs the contract, trade credit is always part of the retailer's financing. With net terms ($d_t^*=0$, $\theta_b^*=0$) the retailer takes no bank loan. With two-part terms ($d_t^*>0$) he finances inventory with both a bank loan and trade credit. This is the paper's main result on the composition of inventory financing portfolios.
--
--   **Formalization Note** The result is stated on the paper's reduced problem (8) over thresholds (p. 13: "we treat $(\theta_b,\theta_t)$ as the supplier's decision variables"). $\Theta$ adds to the printed set of Corollary 3 the constraints $\theta_t\le Q(\theta_b,\theta_t)$ and $c\le w_c$, the image under (11) of §3.1's $c\le w_c\le w_t\le 1$. "No bank loan" is $\theta_b^*=0$, because $\theta_b=(1+r_b)B$ (p. 9). "Trade credit is used" is $\theta_t^*>\theta_b^*$, by (1). "The optimal contract" is read as every maximizer. The paper does not prove that a maximizer exists, and the statement does not assert one. "$K$ sufficiently large" is read below $M^*$: for $K\ge M^*$ the domain has no point with $\theta_t>0$ and the claim would be vacuous. "Sufficiently small" is an interval $(0,\bar K)$. The thresholds $\underline K,\bar K$ may depend on $f,c,\alpha_b,\alpha_t$ but not on the contract.
-- source:
--   Yang & Birge, Trade Credit, Risk Sharing, and Inventory Financing Portfolios, Management Science 64(8) (2018), accepted manuscript (LBS Research Online eprint 801), p. 15, Proposition 3; proof pp. 37–38

import Mathlib
import Definitions.Def_TradeCredit_Terms_Model

namespace TradeCredit.Terms

theorem proposition3_optimal_terms (f : ℝ → ℝ) (hf : DemandModel f)
    (c αb αt : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hαb0 : 0 ≤ αb) (hαb1 : αb ≤ 1)
    (hαt0 : 0 ≤ αt) (hαt1 : αt ≤ 1) :
    -- trade credit is always used when external financing is used
    (∀ K : ℝ, 0 < K → ∀ θb θt : ℝ, IsOptimalContract f c αb αt K θb θt →
        0 < θt → θb < θt) ∧
    -- 1. α_t = 0: net terms, no bank loan
    (αt = 0 → ∀ K : ℝ, 0 < K → ∀ θb θt : ℝ, IsOptimalContract f c αb αt K θb θt →
        θb = 0 ∧ dt f αb θb = 0) ∧
    -- 1. K sufficiently large (below M*): net terms, no bank loan
    (∃ Klow : ℝ, Klow < Mstar f ∧ ∀ K : ℝ, 0 < K → Klow ≤ K → K < Mstar f →
        ∀ θb θt : ℝ, IsOptimalContract f c αb αt K θb θt → θb = 0 ∧ dt f αb θb = 0) ∧
    -- 2. α_t > 0 and K sufficiently small: two-part terms, bank loan and trade credit
    (0 < αt → ∃ Khigh : ℝ, 0 < Khigh ∧ ∀ K : ℝ, 0 < K → K < Khigh →
        ∀ θb θt : ℝ, IsOptimalContract f c αb αt K θb θt →
          0 < θb ∧ θb < θt ∧ 0 < dt f αb θb) := by sorry

end TradeCredit.Terms
