-- Prove2me | Theorems.Thm_RobustMDP_FiniteHorizon_bellman_maps_monotone
-- name    : RobustMDP.FiniteHorizon.bellman_maps_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:19:47.81965+00:00
-- url     : https://prove2.me/theorems/55bad95f-accf-482b-90bf-4305c34bfd62
-- title:
--   Proof of Theorem 1, p. 783 — the maps $g_t$ of problems (15) and (16) are componentwise nondecreasing
-- statement:
--   Consider a finite-horizon robust MDP with nonempty row sets $\mathcal P_i^a\subseteq\Delta_n$. For each stage $t\in T$ define $g_t:\mathbb R^n\to\mathbb R^n$ componentwise, for problem (15), by
--
--   $$
--   (g_t(v))_i:=\min_{a\in\mathcal A}\big(c_t(i,a)+\sigma_{\mathcal P_i^a}(v)\big),\qquad i\in\mathcal X,
--   $$
--
--   and, for a controller policy $\pi=(\mathbf a_t)_{t\in T}$ and problem (16), by
--
--   $$
--   (g_t(v))_i:=c_t(i,\mathbf a_t(i))+\sigma_{\mathcal P_i^{\mathbf a_t(i)}}(v),\qquad i\in\mathcal X .
--   $$
--
--   Both maps are componentwise nondecreasing, for every $t$ and every $\pi$.
--
--   This is the hypothesis of Lemma 1 for problems (15) and (16), which yields recursions (7) and (10).
--
--   **Formalization Note** The minimum over the finite nonempty action set is Lean's `⨅ a`.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 783, proof of Theorem 1, definitions of g_t for (15) and (16)

import Mathlib
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_FiniteHorizon_Model

namespace RobustMDP.FiniteHorizon

/-- (p. 783, proof of Theorem 1.) For every stage `t`, the maps `g_t : ℝⁿ → ℝⁿ` defined by
`(g_t(v))_i := min_{a ∈ 𝒜} (c_t(i, a) + σ_{𝒫_i^a}(v))` (for problem (15)) and, for every
controller policy `π`, `(g_t(v))_i := c_t(i, 𝐚_t(i)) + σ_{𝒫_i^{𝐚_t(i)}}(v)` (for problem (16))
are componentwise nondecreasing. The minimum over the finite nonempty action set is `⨅ a`. -/
theorem bellman_maps_monotone {n N : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n N A) (t : Fin N) :
    Monotone (fun (v : Fin n → ℝ) (i : Fin n) =>
      ⨅ a : A, (M.cost t i a + Shared.supportFunction (M.rows a i) v)) ∧
    ∀ π : ControlPolicy n N A,
      Monotone (fun (v : Fin n → ℝ) (i : Fin n) =>
        M.cost t i (π t i) + Shared.supportFunction (M.rows (π t i) i) v) := by sorry

end RobustMDP.FiniteHorizon
