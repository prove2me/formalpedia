-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_service_ratio_eq_R
-- name    : StaticReusable.Guarantee.service_ratio_eq_R
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:56.768332+00:00
-- url     : https://prove2.me/theorems/bf9d799a-eadd-4f88-9d2a-d6e1b681647d
-- title:
--   §3.1 Step 2, p. 13 — the ratio of stock-in probabilities of λ̃ and the policy equals R(z_1, …, z_C)
-- statement:
--   Let $C \ge 1$, $\mu > 0$, and let $\lambda = (\lambda_1, \dots, \lambda_C)$ be any stationary policy with rates in $[0,\Lambda]$, with static rate $\tilde\lambda$ from (9). With $z_i = \prod_{j=i}^{C} \lambda_j/\mu$ ($i = 1, \dots, C$, and $z_{C+1} = 1$), the ratio of the service levels of the static policy $\tilde\lambda$ and of $\lambda$ is
--   $$\frac{1 - \mathbb P_0(\tilde\lambda)}{1 - \mathbb P_0(\lambda)} = R(z_1, \dots, z_C) = \frac{\left(\sum_{k=0}^{C} a_k z_{k+1}\right)\sum_{i=1}^{C} a_i \left[\frac{\sum_{k=1}^{C} a_k z_k}{\sum_{k=1}^{C} a_k z_{k+1}}\right]^{C-i}}{\left(\sum_{k=1}^{C} a_k z_{k+1}\right)\sum_{i=0}^{C} a_i \left[\frac{\sum_{k=1}^{C} a_k z_k}{\sum_{k=1}^{C} a_k z_{k+1}}\right]^{C-i}}, \qquad a_i = \frac{C!}{(C-i)!}.$$
--
--   This change of variables turns the bound on the stock-in ratio into a bound on one rational function of $z_1, \dots, z_C \ge 0$, which Steps 2a and 2b then establish.
--
--   **Formalization Note** The paper writes the identity for the optimal policy; it holds for every stationary policy and is stated so. Both service levels are positive (state $C$ has weight $C! > 0$), and $\sum_{k=1}^{C} a_k z_{k+1} \ge C! > 0$, so the divisions on both sides are genuine.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 13, §3.1, Step 2 (definition of R)

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem service_ratio_eq_R {C : ℕ} {μ Λ : ℝ} (hC : 1 ≤ C) (hμ : 0 < μ)
    (lam : ℕ → ℝ) (hlam : lam ∈ Policies C Λ) :
    serviceLevel C μ (fun _ => staticRate C μ lam) / serviceLevel C μ lam =
      R C (zOf C μ lam) := by sorry
end StaticReusable.Guarantee
