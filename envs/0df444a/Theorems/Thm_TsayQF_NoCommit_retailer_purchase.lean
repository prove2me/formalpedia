-- Prove2me | Theorems.Thm_TsayQF_NoCommit_retailer_purchase
-- name    : TsayQF.NoCommit.retailer_purchase
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:29.324995+00:00
-- url     : https://prove2.me/theorems/3be9df31-5964-46ff-95b2-9e7166bae33a
-- title:
--   §5.1, (1), p. 1346 — G(r|μ) = (p + s − c)r − sμ − (p + s − u)E[r − X]⁺, and the retailer buys r*_NC = min[μ + z_εσ_ε, Q]
-- statement:
--   Let $p > c > m > 0$, $u < m$, $s \ge 0$ be the costs of Tsay (1999), let $\sigma_\varepsilon \ge 0$, and let $z_\varepsilon = \Phi^{-1}\big((p+s-c)/(p+s-u)\big)$, where $\Phi$ is the standard normal distribution function. Given the signal $\mu$, demand is $X \sim N(\mu, \sigma_\varepsilon^2)$ and the retailer's expected profit from purchase $r$ is
--   $$G(r\mid\mu) = E_{X\mid\mu}\{p\min[X,r] - c\,r - s[X-r]^+ + u[r-X]^+\}.$$
--   Then:
--   1. for every $r$ and $\mu$,
--   $$G(r\mid\mu) = (p+s-c)\,r - s\,\mu - (p+s-u)\,E_{X\mid\mu}\{[r-X]^+\};$$
--   2. for every $\mu$ and every production $Q$, a purchase $r \le Q$ maximizes $G(\cdot\mid\mu)$ over $\{r \le Q\}$ if and only if
--   $$r = r^*_{NC}(Q,\mu) = \min[\mu + z_\varepsilon\sigma_\varepsilon,\ Q].$$
--
--   This is the retailer's step of the backward induction: the EM's production problem anticipates this purchase.
--
--   **Formalization Note** $z_\varepsilon$ enters as a real number $z$ with the hypothesis $\Phi(z) = (p+s-c)/(p+s-u)$; since $\Phi$ is continuous and strictly increasing it exists and is unique. The case $\sigma_\varepsilon = 0$ is included (then $X = \mu$). The constraint $r \le Q$ appears in the conjunction because a maximizer over $\{r \le Q\}$ is required to be feasible.
-- source:
--   Tsay, The quantity flexibility contract and supplier-customer incentives, Management Science 45(10) (1999), p. 1346, §5.1, (1)

import Mathlib
import Definitions.Def_TsayQF_NoCommit_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TsayQF.NoCommit

theorem retailer_purchase (D : Data) (v : ℝ≥0) (z : ℝ)
    (hz : cdf (gaussianReal 0 1) z = kR D) :
    (∀ r μ : ℝ, G D v r μ = (D.p + D.s - D.c) * r - D.s * μ
        - (D.p + D.s - D.u) * ∫ x, max (r - x) 0 ∂(gaussianReal μ v)) ∧
      ∀ μ Q r : ℝ, (r ≤ Q ∧ IsMaxOn (fun r' => G D v r' μ) (Set.Iic Q) r) ↔
        r = ncPurchase v z μ Q := by sorry

end TsayQF.NoCommit
