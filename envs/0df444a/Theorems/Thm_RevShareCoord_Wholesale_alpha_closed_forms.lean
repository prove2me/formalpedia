-- Prove2me | Theorems.Thm_RevShareCoord_Wholesale_alpha_closed_forms
-- name    : RevShareCoord.Wholesale.alpha_closed_forms
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:07:00.357734+00:00
-- url     : https://prove2.me/theorems/ec5e3c02-54a6-47ef-8893-b4348bfcc64e
-- title:
--   Sec. 4.1.1, p. 18 — closed forms for q*, q_I and the profits when R′(q) = 1 − q^α
-- statement:
--   Let $\alpha > 0$ and $0 < c < 1$, and take the revenue function $R(q) = q - q^{\alpha+1}/(\alpha+1)$ on $[0,1]$, whose marginal revenue is $R'(q) = 1 - q^\alpha$. With the supplier's profit $\pi_s(q) = q(R'(q) - c)$, the retailer's profit $\pi_r(q) = R(q) - qR'(q)$ and the supply chain profit $\Pi(q) = R(q) - qc$:
--
--   1. $q^* = \left(\frac{1-c}{1+\alpha}\right)^{1/\alpha}$ lies in $[0,1]$ and is the unique maximizer of $\pi_s$ on $[0,1]$;
--   2. $q_I = (1-c)^{1/\alpha}$ lies in $[0,1]$ and is the unique maximizer of $\Pi$ on $[0,1]$;
--   3. the resulting profits are
--
--   $$
--   \pi_r(q^*) = \frac{\alpha}{1+\alpha}\left(\frac{1-c}{1+\alpha}\right)^{\frac{1+\alpha}{\alpha}}, \qquad
--   \pi_s(q^*) = \alpha\left(\frac{1-c}{1+\alpha}\right)^{\frac{1+\alpha}{\alpha}}, \qquad
--   \Pi(q_I) = \frac{\alpha}{1+\alpha}\,(1-c)^{\frac{1+\alpha}{\alpha}} .
--   $$
--
--   The family covers convex ($\alpha < 1$), linear ($\alpha = 1$) and concave ($\alpha > 1$) marginal revenue, and gives the efficiency and profit share of the wholesale-price contract in closed form.
--
--   **Formalization Note** $R'$ is not given separately: it is the derivative `deriv` of $R$, which equals $1 - q^\alpha$ on $[0,1]$. The powers are real powers. The range $0 < c < 1$ is implicit on the page ($c > 0$ from the model and $R'(0) = 1 > c$ for viability) and is needed for $q^*, q_I \in (0,1)$. Following the page, quantities range over $[0,1]$.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 18 (PDF 19), Section 4.1.1, example R'(q) = 1 - q^α: displays of q*, q_I, π_r(q*), π_s(q*), Π(q_I)

import Mathlib
import Definitions.Def_RevShareCoord_Wholesale_Model

namespace RevShareCoord.Wholesale

/-- Sec. 4.1.1 (p. 18): with `R(q) = q − q^{α+1}/(α+1)` (so `R'(q) = 1 − q^α`) on `[0, 1]`,
`α > 0` and `0 < c < 1`, the supplier's optimal quantity to induce is the unique maximizer
`q* = ((1−c)/(1+α))^{1/α}` of `π_s` on `[0, 1]`, the integrated-channel quantity is the
unique maximizer `q_I = (1−c)^{1/α}` of `Π` on `[0, 1]`, and
`π_r(q*) = (α/(1+α)) ((1−c)/(1+α))^{(1+α)/α}`, `π_s(q*) = α ((1−c)/(1+α))^{(1+α)/α}`,
`Π(q_I) = (α/(1+α)) (1−c)^{(1+α)/α}`. -/
theorem alpha_closed_forms (α c : ℝ) (hα : 0 < α) (hc0 : 0 < c) (hc1 : c < 1) :
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
    retailerProfit (alphaRevenue α) (deriv (alphaRevenue α)) (((1 - c) / (1 + α)) ^ (1 / α)) =
      α / (1 + α) * ((1 - c) / (1 + α)) ^ ((1 + α) / α) ∧
    supplierProfit (deriv (alphaRevenue α)) c (((1 - c) / (1 + α)) ^ (1 / α)) =
      α * ((1 - c) / (1 + α)) ^ ((1 + α) / α) ∧
    chainProfit (alphaRevenue α) c ((1 - c) ^ (1 / α)) =
      α / (1 + α) * (1 - c) ^ ((1 + α) / α) := by sorry

end RevShareCoord.Wholesale
