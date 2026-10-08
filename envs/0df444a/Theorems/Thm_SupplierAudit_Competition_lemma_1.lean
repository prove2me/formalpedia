-- Prove2me | Theorems.Thm_SupplierAudit_Competition_lemma_1
-- name    : SupplierAudit.Competition.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:27.22419+00:00
-- url     : https://prove2.me/theorems/b0262383-e196-443d-9f6d-e21e4ddafe25
-- title:
--   Lemma 1 — equilibrium ex post sourcing quantities and profits of the buyers
-- statement:
--   Consider the stage-2 game in which buyer $B_i$ with $n_i$ offending suppliers has demand intercept $A(n_i)$ ($\alpha$ if $n_i = 0$, $\alpha - d_M$ otherwise) and unit cost $c(n_i) = (2-n_i)w + n_i\hat w$, and the buyers play the linear differentiated Cournot duopoly with substitution parameter $\beta \in [0,1]$. Under the standing assumptions of the model, for each of the five scenarios with $n_1 \le n_2$ the unique pure Nash equilibrium $(q^*_1, q^*_2)$ is:
--
--   | $(n_1,n_2)$ | $q^*_1$ | $q^*_2$ |
--   |---|---|---|
--   | $(0,0)$ | $\frac{\alpha-2w}{2+\beta}$ | $\frac{\alpha-2w}{2+\beta}$ |
--   | $(0,1)$ | $\frac{\alpha}{2+\beta} + \frac{\beta d_M-(4-\beta)w+\beta\hat w}{4-\beta^2}$ | $\frac{\alpha}{2+\beta} - \frac{2d_M+2(1-\beta)w+2\hat w}{4-\beta^2}$ |
--   | $(1,1)$ | $\frac{\alpha-d_M-w-\hat w}{2+\beta}$ | $\frac{\alpha-d_M-w-\hat w}{2+\beta}$ |
--   | $(1,2)$ | $\frac{\alpha-d_M}{2+\beta} - \frac{2w+2(1-\beta)\hat w}{4-\beta^2}$ | $\frac{\alpha-d_M}{2+\beta} - \frac{(4-\beta)\hat w-\beta w}{4-\beta^2}$ |
--   | $(2,2)$ | $\frac{\alpha-d_M-2\hat w}{2+\beta}$ | $\frac{\alpha-d_M-2\hat w}{2+\beta}$ |
--
--   Moreover, for every realizable pair $(n_1,n_2)$ (both at most $2$, differing by at most $1$, in either order), the closed-form quantities $q^*_1(n_1,n_2)$ and $q^*_1(n_2,n_1)$ of the model are strictly positive, form a Nash equilibrium, and buyer $B_1$'s equilibrium payoff equals the model's stage-2 profit
--   $$\pi^b_1(n_1,n_2) = q^*_1(n_1,n_2)^2 .$$
--
--   Together with uniqueness, this shows that the model's stage-2 profits are exactly the equilibrium profits of the table, the squares of the quantities.
--
--   **Formalization Note** The page tabulates the case $n_2 \ge n_1$ and says the other case is symmetric; the second part of the statement covers both orders. Strict positivity of the quantities is the purpose of the three conditions of p. 8 and is stated explicitly.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), Lemma 1, p. 9; proof p. ec3 (PDF 31)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

namespace SupplierAudit.Competition

theorem lemma_1 (P : Params) :
    (∀ q₁ q₂ : ℝ,
      IsCournotNash P.β (intercept P 0) (unitCost P 0) (intercept P 0) (unitCost P 0) q₁ q₂ ↔
        q₁ = (P.α - 2 * P.w) / (2 + P.β) ∧ q₂ = (P.α - 2 * P.w) / (2 + P.β)) ∧
    (∀ q₁ q₂ : ℝ,
      IsCournotNash P.β (intercept P 0) (unitCost P 0) (intercept P 1) (unitCost P 1) q₁ q₂ ↔
        q₁ = P.α / (2 + P.β) + (P.β * P.dM - (4 - P.β) * P.w + P.β * P.wh) / (4 - P.β ^ 2) ∧
        q₂ = P.α / (2 + P.β) - (2 * P.dM + 2 * (1 - P.β) * P.w + 2 * P.wh) / (4 - P.β ^ 2)) ∧
    (∀ q₁ q₂ : ℝ,
      IsCournotNash P.β (intercept P 1) (unitCost P 1) (intercept P 1) (unitCost P 1) q₁ q₂ ↔
        q₁ = (P.α - P.dM - P.w - P.wh) / (2 + P.β) ∧ q₂ = (P.α - P.dM - P.w - P.wh) / (2 + P.β)) ∧
    (∀ q₁ q₂ : ℝ,
      IsCournotNash P.β (intercept P 1) (unitCost P 1) (intercept P 2) (unitCost P 2) q₁ q₂ ↔
        q₁ = (P.α - P.dM) / (2 + P.β) - (2 * P.w + 2 * (1 - P.β) * P.wh) / (4 - P.β ^ 2) ∧
        q₂ = (P.α - P.dM) / (2 + P.β) - ((4 - P.β) * P.wh - P.β * P.w) / (4 - P.β ^ 2)) ∧
    (∀ q₁ q₂ : ℝ,
      IsCournotNash P.β (intercept P 2) (unitCost P 2) (intercept P 2) (unitCost P 2) q₁ q₂ ↔
        q₁ = (P.α - P.dM - 2 * P.wh) / (2 + P.β) ∧ q₂ = (P.α - P.dM - 2 * P.wh) / (2 + P.β)) ∧
    (∀ n₁ n₂ : ℕ, n₁ ≤ 2 → n₂ ≤ 2 → n₁ ≤ n₂ + 1 → n₂ ≤ n₁ + 1 →
      0 < stage2q P n₁ n₂ ∧
      IsCournotNash P.β (intercept P n₁) (unitCost P n₁) (intercept P n₂) (unitCost P n₂)
        (stage2q P n₁ n₂) (stage2q P n₂ n₁) ∧
      cournotPayoff P.β (intercept P n₁) (unitCost P n₁) (stage2q P n₁ n₂) (stage2q P n₂ n₁) =
        stage2Profit P n₁ n₂) := by sorry

end SupplierAudit.Competition
