-- Prove2me | Theorems.Thm_PDASNewton_Local_lemma_3_1
-- name    : PDASNewton.Local.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:08:35.987754+00:00
-- url     : https://prove2.me/theorems/904b22a8-354a-4aec-bb78-85dcaa18b8b5
-- title:
--   Lemma 3.1, p. 6 — y ↦ max(0, y) is slantly differentiable on ℝⁿ with slanting function G_m for every δ
-- statement:
--   Fix $\delta \in \mathbb{R}^n$ and let $G_m(y) = \operatorname{diag}(g_1(y_1), \dots, g_n(y_n))$ as in (3.2), where $g_i(z) = 0$ for $z < 0$, $g_i(z) = 1$ for $z > 0$ and $g_i(0) = \delta_i$. Then the componentwise maximum $y \mapsto \max(0, y)$ from $\mathbb{R}^n$ to $\mathbb{R}^n$ is slantly differentiable on $\mathbb{R}^n$ with slanting function $G_m$: for every $y \in \mathbb{R}^n$,
--   $$\lim_{h \to 0} \frac{1}{\|h\|}\,\bigl\|\max(0, y + h) - \max(0, y) - G_m(y + h)h\bigr\| = 0.$$
--
--   The value of $G_m$ where a coordinate vanishes is arbitrary; the semismooth Newton method of the paper uses $\delta = 0$.
--
--   **Formalization Note** $\mathbb{R}^n$ is `Fin n → ℝ` with the sup norm; the limit is stated as a little-o relation.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 6, (3.2) and Lemma 3.1

import Mathlib
import Definitions.Def_PDASNewton_Local_Setting

namespace PDASNewton.Local

/-- Lemma 3.1, p. 6: the map `y ↦ max(0, y)` from `ℝⁿ` to `ℝⁿ` (componentwise) is slantly
differentiable on `ℝⁿ`, and `G_m` of (3.2) is a slanting function for every `δ ∈ ℝⁿ`. -/
theorem lemma_3_1 {n : ℕ} (δ : Fin n → ℝ) :
    IsSlantingFunction (fun y : Fin n → ℝ => fun i => max 0 (y i)) (Gm δ) Set.univ := by sorry

end PDASNewton.Local
