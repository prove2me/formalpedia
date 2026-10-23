-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_eq_11
-- name    : StaticReusable.Guarantee.eq_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:51.420907+00:00
-- url     : https://prove2.me/theorems/0ffae6c6-f9a1-4186-970b-a3ccd1122c4a
-- title:
--   Eq. (11), p. 12 — the market share of the static rate λ̃ relative to the policy's equals the ratio of stock-in probabilities
-- statement:
--   Let $C \in \mathbb N$, $\mu > 0$, and let $\lambda = (\lambda_1, \dots, \lambda_C)$ be any stationary policy with rates in $[0,\Lambda]$. Let $\tilde\lambda = \sum_{i=1}^C \lambda_i \mathbb P_i(\lambda) / \sum_{i=1}^C \mathbb P_i(\lambda)$ be its static rate (9), and write $\mathcal{MS}^{\tilde\lambda}$, $\mathcal{SL}^{\tilde\lambda}$ for the market share and service level of the static policy with rate $\tilde\lambda$. Then
--   $$\frac{\mathcal{MS}^{\tilde\lambda}}{\mathcal{MS}^{\lambda}} = \frac{1 - \mathbb P_0(\tilde\lambda)}{1 - \mathbb P_0(\lambda)} = \frac{\mathcal{SL}^{\tilde\lambda}}{\mathcal{SL}^{\lambda}},$$
--   stated without division as
--   $$\mathcal{MS}^{\tilde\lambda}\cdot \mathcal{SL}^{\lambda} = \mathcal{MS}^{\lambda}\cdot \mathcal{SL}^{\tilde\lambda}.$$
--
--   This is the first part of Step 1 of the proof of Theorem 1: for market share, the guarantee of the static rate $\tilde\lambda$ is exactly the ratio of the service levels.
--
--   **Formalization Note** The page states (11) for the optimal policy $\pi^*$, but its derivation uses only (6) and (9); the statement holds for every stationary policy and is stated so. The ratio is cross-multiplied because the market share of a policy can be $0$ (when $\lambda_C = 0$), where real division would return the junk value $0$.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 12, eq. (11) (with (6), (9))

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem eq_11 {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) (lam : ℕ → ℝ) (hlam : lam ∈ Policies C Λ) :
    marketShare C μ (fun _ => staticRate C μ lam) * serviceLevel C μ lam =
      marketShare C μ lam * serviceLevel C μ (fun _ => staticRate C μ lam) := by sorry
end StaticReusable.Guarantee
