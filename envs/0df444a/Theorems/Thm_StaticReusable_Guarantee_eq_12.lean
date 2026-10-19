-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_eq_12
-- name    : StaticReusable.Guarantee.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:56.796595+00:00
-- url     : https://prove2.me/theorems/9b11cfef-689a-4d43-a9b5-8ecdfb63f1cd
-- title:
--   Eq. (12), p. 13 — the profit of the static rate λ̃ relative to the policy's is at least the ratio of stock-in probabilities
-- statement:
--   Let the instance satisfy the standing assumptions of $\Omega$ (in particular, $\lambda \mapsto \lambda(p(\lambda) - c)$ is concave on $[0,\Lambda]$), and let $\lambda = (\lambda_1, \dots, \lambda_C)$ be any stationary policy with rates in $[0,\Lambda]$, with static rate $\tilde\lambda$ from (9). Then $\tilde\lambda \in [0,\Lambda]$, and
--   $$\frac{\mathcal P^{\tilde\lambda}}{\mathcal P^{\lambda}} \ge \frac{1 - \mathbb P_0(\tilde\lambda)}{1 - \mathbb P_0(\lambda)}\quad\text{in the form}\quad \mathcal P^{\lambda}\cdot \mathcal{SL}^{\tilde\lambda} \le \mathcal P^{\tilde\lambda}\cdot \mathcal{SL}^{\lambda}.$$
--
--   The inequality is Jensen's inequality for the concave profit rate, applied to the random rate that equals $\lambda_i$ with probability $\mathbb P_i/(1 - \mathbb P_0)$, whose mean is $\tilde\lambda$. It is the profit part of Step 1 of the proof of Theorem 1.
--
--   **Formalization Note** As for (11), the page writes the optimal policy but uses no optimality; the statement is for every stationary policy. The cross-multiplied form is the page's ratio inequality whenever $\mathcal P^{\lambda} > 0$, and it remains meaningful (and true) when $\mathcal P^{\lambda} \le 0$, since both service levels are positive. The conjunct $\tilde\lambda \in [0,\Lambda]$ records that the static rate is itself a feasible rate.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 13, eq. (12) (with (5), (9) and Jensen's inequality)

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem eq_12 {C : ℕ} {μ Λ c α₁ α₂ α₃ : ℝ} {p : ℝ → ℝ}
    (hS : Standing C μ Λ c p α₁ α₂ α₃) (lam : ℕ → ℝ) (hlam : lam ∈ Policies C Λ) :
    staticRate C μ lam ∈ Set.Icc 0 Λ ∧
      profit C μ p c lam * serviceLevel C μ (fun _ => staticRate C μ lam) ≤
        profit C μ p c (fun _ => staticRate C μ lam) * serviceLevel C μ lam := by sorry
end StaticReusable.Guarantee
