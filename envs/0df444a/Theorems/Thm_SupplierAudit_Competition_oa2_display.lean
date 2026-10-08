-- Prove2me | Theorems.Thm_SupplierAudit_Competition_oa2_display
-- name    : SupplierAudit.Competition.oa2_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:10.36002+00:00
-- url     : https://prove2.me/theorems/8c9aa462-dd8b-434c-9a35-984771dbebe0
-- title:
--   OA.2 — the expected profit $\Pi^b_1$ grouped by damage outcome
-- statement:
--   Write $\lambda_I(x) = r(1-e)(1-x)$ and $\lambda_C(x_1,x_2) = r(1-e)(1-x_1)(1-x_2)$, and abbreviate $\lambda_I^1 = \lambda_I(e_{11})$, $\lambda_C = \lambda_C(e_{1c},e_{2c})$, $\lambda_I^2 = \lambda_I(e_{22})$. For all efforts $e_{11}, e_{1c}, e_{22}, e_{2c} \in [0,1]$ and every fixed cost $K$, buyer $B_1$'s expected profit is
--
--   $$\begin{aligned}\Pi^b_1(e_{11},e_{1c};e_{22},e_{2c}) ={}& [1-\lambda_I^1][1-\lambda_C][1-\lambda_I^2]\Big(\tfrac{\alpha-2w}{2+\beta}\Big)^2 + [1-\lambda_I^1][1-\lambda_C]\lambda_I^2\Big(\tfrac{\alpha}{2+\beta}+\tfrac{\beta d_M-(4-\beta)w+\beta\hat w}{4-\beta^2}\Big)^2\\ &+ \lambda_I^1[1-\lambda_C][1-\lambda_I^2]\Big(\tfrac{\alpha}{2+\beta}-\tfrac{2d_M+2(1-\beta)w+2\hat w}{4-\beta^2}\Big)^2\\ &+ \big\{[1-\lambda_I^1]\lambda_C[1-\lambda_I^2] + \lambda_I^1[1-\lambda_C]\lambda_I^2\big\}\Big(\tfrac{\alpha-d_M-w-\hat w}{2+\beta}\Big)^2\\ &+ [1-\lambda_I^1]\lambda_C\lambda_I^2\Big(\tfrac{\alpha-d_M}{2+\beta}-\tfrac{2w+2(1-\beta)\hat w}{4-\beta^2}\Big)^2 + \lambda_I^1\lambda_C[1-\lambda_I^2]\Big(\tfrac{\alpha-d_M}{2+\beta}-\tfrac{(4-\beta)\hat w-\beta w}{4-\beta^2}\Big)^2\\ &+ \lambda_I^1\lambda_C\lambda_I^2\Big(\tfrac{\alpha-d_M-2\hat w}{2+\beta}\Big)^2 - \big[K\mathbb 1_{e_{11}>0}+\tfrac a2 e_{11}^2\big] - \big[K\mathbb 1_{e_{1c}>0}+\tfrac a2 e_{1c}^2\big].\end{aligned}$$
--
--   The model defines $\Pi^b_1$ as the expectation over the eight independent damage outcomes; this identity groups the outcomes by the resulting stage-2 scenario and inserts Lemma 1's profits. It is the formula every later computation in the e-companion starts from.
-- source:
--   Chen, Qi, Dawande, Supplier Centrality and Auditing Priority in Socially-Responsible Supply Chains, accepted manuscript (SSRN 2889889), OA.2 (unnumbered display), p. ec1 (PDF 29)

import Mathlib
import Definitions.Def_SupplierAudit_Competition_Model

namespace SupplierAudit.Competition

theorem oa2_display (P : Params) (K e11 e1c e22 e2c : ℝ)
    (h11 : e11 ∈ Set.Icc (0 : ℝ) 1) (h1c : e1c ∈ Set.Icc (0 : ℝ) 1)
    (h22 : e22 ∈ Set.Icc (0 : ℝ) 1) (h2c : e2c ∈ Set.Icc (0 : ℝ) 1) :
    expProfit₁ P K e11 e1c e22 e2c =
      (1 - lamI P e11) * (1 - lamC P e1c e2c) * (1 - lamI P e22) *
          ((P.α - 2 * P.w) / (2 + P.β)) ^ 2
      + (1 - lamI P e11) * (1 - lamC P e1c e2c) * lamI P e22 *
          (P.α / (2 + P.β) + (P.β * P.dM - (4 - P.β) * P.w + P.β * P.wh) / (4 - P.β ^ 2)) ^ 2
      + lamI P e11 * (1 - lamC P e1c e2c) * (1 - lamI P e22) *
          (P.α / (2 + P.β) - (2 * P.dM + 2 * (1 - P.β) * P.w + 2 * P.wh) / (4 - P.β ^ 2)) ^ 2
      + ((1 - lamI P e11) * lamC P e1c e2c * (1 - lamI P e22)
          + lamI P e11 * (1 - lamC P e1c e2c) * lamI P e22) *
          ((P.α - P.dM - P.w - P.wh) / (2 + P.β)) ^ 2
      + (1 - lamI P e11) * lamC P e1c e2c * lamI P e22 *
          ((P.α - P.dM) / (2 + P.β) - (2 * P.w + 2 * (1 - P.β) * P.wh) / (4 - P.β ^ 2)) ^ 2
      + lamI P e11 * lamC P e1c e2c * (1 - lamI P e22) *
          ((P.α - P.dM) / (2 + P.β) - ((4 - P.β) * P.wh - P.β * P.w) / (4 - P.β ^ 2)) ^ 2
      + lamI P e11 * lamC P e1c e2c * lamI P e22 *
          ((P.α - P.dM - 2 * P.wh) / (2 + P.β)) ^ 2
      - ((if 0 < e11 then K else 0) + P.a / 2 * e11 ^ 2)
      - ((if 0 < e1c then K else 0) + P.a / 2 * e1c ^ 2) := by sorry

end SupplierAudit.Competition
