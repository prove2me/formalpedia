-- Prove2me | Theorems.Thm_RobustMDP_Discounted_bellmanOps_monotone_contractive
-- name    : RobustMDP.Discounted.bellmanOps_monotone_contractive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:58:34.978639+00:00
-- url     : https://prove2.me/theorems/4a91064b-96d2-4feb-810a-90f244b8135e
-- title:
--   Eqs. (29)–(30), p. 786 — the robust Bellman maps are nondecreasing and $\nu$-contractive
-- statement:
--   In the discounted robust MDP, the robust Bellman operator $g$ of (29),
--   $$(g(v))_i = \min_{a \in \mathcal A} \big(c(i, a) + \nu\, \sigma_{\mathcal P_i^a}(v)\big),$$
--   and, for every stationary policy $\pi = (\mathbf a, \mathbf a, \dots)$, the policy-evaluation operator $g_\pi$ of (30),
--   $$(g_\pi(v))_i = c(i, \mathbf a(i)) + \nu\, \sigma_{\mathcal P_i^{\mathbf a(i)}}(v),$$
--   are componentwise nondecreasing, and satisfy
--   $$\|g(u) - g(v)\|_\infty \le \nu \|u - v\|_\infty, \qquad \|g_\pi(u) - g_\pi(v)\|_\infty \le \nu \|u - v\|_\infty$$
--   for all $u, v \in \mathbb R^n$.
--
--   Only the inclusions $\mathcal P_i^a \subseteq \Delta_n$ and nonemptiness of the row sets are used. With Lemma 2, these properties identify the values of (27) and (28) with the fixed points of $g$ and $g_\pi$.
--
--   **Formalization Note** $\mathbb R^n$ is `Fin n → ℝ`, whose Mathlib metric is the sup metric, so $\nu$-contractivity is `LipschitzWith ν`. Monotonicity is for the componentwise order.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 786, Eqs. (29)–(30) and the display that follows them

import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_Discounted_bellmanOps

namespace RobustMDP.Discounted

/-- Nilim–El Ghaoui 2005, p. 786: the maps `g` of (29) (the robust Bellman operator) and of (30)
(robust evaluation of a stationary policy `π`) are componentwise nondecreasing and `ν`-contractive
in the sup norm `‖·‖_∞` (the sup metric of `Fin n → ℝ`): for all `u, v ∈ ℝⁿ`,
`‖g(u) − g(v)‖_∞ ≤ ν ‖u − v‖_∞`. Only `𝒫_i^a ⊆ Δ_n` and nonemptiness of the row sets are
assumed. -/
theorem bellmanOps_monotone_contractive {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) :
    (Monotone M.bellmanOp ∧ LipschitzWith ⟨M.discount, M.discount_nonneg⟩ M.bellmanOp) ∧
    ∀ π : StationaryPolicy n A,
      Monotone (M.policyOp π) ∧ LipschitzWith ⟨M.discount, M.discount_nonneg⟩ (M.policyOp π) := by sorry

end RobustMDP.Discounted
