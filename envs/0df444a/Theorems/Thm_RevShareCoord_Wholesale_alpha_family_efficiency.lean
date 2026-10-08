-- Prove2me | Theorems.Thm_RevShareCoord_Wholesale_alpha_family_efficiency
-- name    : RevShareCoord.Wholesale.alpha_family_efficiency
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:07:14.603757+00:00
-- url     : https://prove2.me/theorems/e5f62352-7439-44f2-a940-d08b401e8af8
-- title:
--   Sec. 4.1.1, p. 18 — with R′(q) = 1 − q^α the wholesale-price contract has efficiency (2+α)/(1+α)^((1+α)/α)
-- statement:
--   Let $\alpha > 0$ and $0 < c < 1$, and take the revenue function $R(q) = q - q^{\alpha+1}/(\alpha+1)$ on $[0,1]$, so that marginal revenue is $R'(q) = 1 - q^\alpha$. Let $\pi_s(q) = q(R'(q) - c)$ be the supplier's profit when she induces the order $q$ with the wholesale price $R'(q)$, $\pi_r(q) = R(q) - qR'(q)$ the retailer's profit, and $\Pi(q) = R(q) - qc$ the supply chain profit. Then:
--
--   1. $q^* = \left(\frac{1-c}{1+\alpha}\right)^{1/\alpha}$ is the unique maximizer of $\pi_s$ on $[0,1]$;
--   2. $q_I = (1-c)^{1/\alpha}$ is the unique maximizer of $\Pi$ on $[0,1]$;
--   3. the supplier's profit share is $\pi_s(q^*)/\Pi(q^*) = (1+\alpha)/(2+\alpha)$;
--   4. the efficiency of the wholesale-price contract is
--
--   $$
--   \frac{\pi_s(q^*) + \pi_r(q^*)}{\Pi(q_I)} = \frac{2+\alpha}{(1+\alpha)^{\frac{1+\alpha}{\alpha}}} ;
--   $$
--
--   5. as a function of $\alpha$ (for the fixed $c$), this efficiency is strictly increasing on $(0,\infty)$, tends to $2/e$ as $\alpha \to 0^+$, and tends to $1$ as $\alpha \to \infty$.
--
--   The result quantifies the cost of double marginalization: the supplier's best wholesale-price contract always loses a fixed fraction of the channel's optimal profit, between $1 - 2/e$ and $0$, and the loss shrinks as the marginal revenue curve becomes more concave.
--
--   **Formalization Note** $R'$ is the derivative `deriv` of $R$, not a separate function. In item 5 the efficiency is the profit ratio of item 4, computed from $R$ at the quantities of items 1–2 (the definition `alphaEfficiency`), not the closed form. The page says "Efficiency is a decreasing function of $\alpha$"; that is a slip, and the corrected increasing form is stated (see the companion statement on $E(\alpha)$). The range $0 < c < 1$ is implicit on the page.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 18 (PDF 19), Section 4.1.1, from 'To illustrate these results, suppose R'(q) = 1 - q^α' to 'the system is coordinated in the limit'

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

namespace RevShareCoord.Wholesale

/-- Sec. 4.1.1 (p. 18): in the `α`-family `R(q) = q − q^{α+1}/(α+1)` on `[0, 1]` with
`α > 0` and `0 < c < 1`, the supplier's optimal quantity to induce
`q* = ((1−c)/(1+α))^{1/α}` and the integrated quantity `q_I = (1−c)^{1/α}` are the unique
maximizers on `[0, 1]` of `π_s` and `Π`; the supplier's profit share is `(1+α)/(2+α)`;
the efficiency is `(2+α)/(1+α)^{(1+α)/α}`; and the efficiency, as a function of `α`, is
strictly increasing on `(0, ∞)`, tends to `2/e` as `α → 0⁺` and to `1` as `α → ∞`. -/
theorem alpha_family_efficiency (α c : ℝ) (hα : 0 < α) (hc0 : 0 < c) (hc1 : c < 1) :
    (((1 - c) / (1 + α)) ^ (1 / α) ∈ Set.Icc (0 : ℝ) 1 ∧
      IsMaxOn (supplierProfit (deriv (alphaRevenue α)) c) (Set.Icc 0 1)
        (((1 - c) / (1 + α)) ^ (1 / α)) ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1,
        IsMaxOn (supplierProfit (deriv (alphaRevenue α)) c) (Set.Icc 0 1) q →
          q = ((1 - c) / (1 + α)) ^ (1 / α)) ∧
    ((1 - c) ^ (1 / α) ∈ Set.Icc (0 : ℝ) 1 ∧
      IsMaxOn (chainProfit (alphaRevenue α) c) (Set.Icc 0 1) ((1 - c) ^ (1 / α)) ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1,
        IsMaxOn (chainProfit (alphaRevenue α) c) (Set.Icc 0 1) q → q = (1 - c) ^ (1 / α)) ∧
    profitShare (alphaRevenue α) (deriv (alphaRevenue α)) c (((1 - c) / (1 + α)) ^ (1 / α)) =
      (1 + α) / (2 + α) ∧
    alphaEfficiency α c = (2 + α) / (1 + α) ^ ((1 + α) / α) ∧
    StrictMonoOn (fun a : ℝ => alphaEfficiency a c) (Set.Ioi 0) ∧
    Filter.Tendsto (fun a : ℝ => alphaEfficiency a c) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (2 / Real.exp 1)) ∧
    Filter.Tendsto (fun a : ℝ => alphaEfficiency a c) Filter.atTop (nhds 1) := by sorry

end RevShareCoord.Wholesale
