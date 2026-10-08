-- Prove2me | Theorems.Thm_QiNonsmoothEq_Attraction_lemma_2_4
-- name    : QiNonsmoothEq.Attraction.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:21:04.337901+00:00
-- url     : https://prove2.me/theorems/c2fd390d-339c-4446-b003-1c3828615c86
-- title:
--   Lemma 2.4, p. 232 — at a BD-regular point, ‖h‖ ≤ c‖F′(x; h)‖ for all h
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^m$ be locally Lipschitz and BD-regular at $x$, that is, directionally differentiable at $x$ with $F'(x;h)\neq 0$ for all $h\neq 0$. Then there is a constant $c$ such that for every $h\in\mathbb R^n$,
--   $$\|h\|\ \le\ c\,\|F'(x;h)\|. \tag{2.11}$$
--
--   BD-regularity says the directional derivative does not vanish off the origin; this lemma upgrades it to a quantitative lower bound, which is the form used in the attraction theorem (Theorem 5.1) as (5.3).
--
--   **Formalization Note** $\mathbb R^n$ and $\mathbb R^m$ are Euclidean spaces with the 2-norm. Local Lipschitz continuity is the paper's standing assumption (§1).
-- source:
--   Qi, Convergence analysis of some algorithms for solving nonsmooth equations, Math. Oper. Res. 18 (1993), p. 232, Lemma 2.4, (2.11)

import Mathlib
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_QiNonsmoothEq_Attraction_Setting
open Filter Topology NonsmoothNewton.Local

namespace QiNonsmoothEq.Attraction

/-- Qi 1993, Lemma 2.4, p. 232: if the locally Lipschitz `F : ℝⁿ → ℝᵐ` is BD-regular at `x`,
there is a constant `c` with `‖h‖ ≤ c ‖F'(x; h)‖` for every `h` (2.11). -/
theorem lemma_2_4 {n m : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (hF : LocallyLipschitz F)
    (x : EuclideanSpace ℝ (Fin n)) (hreg : BDRegularAt F x) :
    ∃ c : ℝ, ∀ h : EuclideanSpace ℝ (Fin n), ‖h‖ ≤ c * ‖dirDeriv F x h‖ := by sorry

end QiNonsmoothEq.Attraction
