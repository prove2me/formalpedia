-- Prove2me | Theorems.Thm_WardropTraffic_EqualTimes_flow_eq_of_used
-- name    : WardropTraffic.EqualTimes.flow_eq_of_used
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:07.413603+00:00
-- url     : https://prove2.me/theorems/f7abf7a6-bbe0-4f44-be05-7fc61160b7bd
-- title:
--   (23), p. 345 — on every used route qᵢ = pᵢ(1 − bᵢ/t)
-- statement:
--   Consider $D$ routes with positive constants $b_i, p_i$ and journey times $t_i(x) = b_i/(1 - x/p_i)$. Let $q$ be a feasible split of $Q$ satisfying the equal-times criterion (1) with common time $t$. Then on every route in use,
--   $$
--   q_i > 0 \implies q_i = p_i\Bigl(1 - \frac{b_i}{t}\Bigr),
--   $$
--   which is equation (23), obtained by solving $t = b_i/(1 - q_i/p_i)$ for $q_i$.
--
--   **Formalization Note** The routes $i = 1, \dots, j$ of (23) are the routes in use; by the companion milestones these are exactly the routes with $b_i < t$, where $t > b_i > 0$, so the division by $t$ is genuine.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 345, (23)

import Mathlib
import Definitions.Def_WardropTraffic_EqualTimes_Setting

namespace WardropTraffic.EqualTimes

theorem flow_eq_of_used {D : ℕ} (b p : Fin D → ℝ) (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i)
    (Q t : ℝ) (q : Fin D → ℝ) (h : IsEqualTimes b p Q q t) :
    ∀ i, 0 < q i → q i = p i * (1 - b i / t) := by sorry

end WardropTraffic.EqualTimes
