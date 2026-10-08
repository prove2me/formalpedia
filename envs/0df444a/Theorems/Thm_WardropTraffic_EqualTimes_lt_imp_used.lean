-- Prove2me | Theorems.Thm_WardropTraffic_EqualTimes_lt_imp_used
-- name    : WardropTraffic.EqualTimes.lt_imp_used
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:53:08.473992+00:00
-- url     : https://prove2.me/theorems/91613ab3-ec94-4e84-bc81-ed5afce67a18
-- title:
--   p. 345 — under equal times t, every route with bᵢ < t is in use
-- statement:
--   Consider $D$ routes with positive constants $b_i, p_i$ and journey times $t_i(x) = b_i/(1 - x/p_i)$. Let $q$ be a feasible split of $Q$ satisfying the equal-times criterion (1) with common time $t$ (used routes have time $t$; unused routes have $t \le b_i$). Then for every route $i$,
--   $$
--   b_i < t \implies q_i > 0 .
--   $$
--   In the paper's labelling, all of the first $j$ routes must be in use: otherwise $t$ would exceed $b_i$ on an unused route.
--
--   **Formalization Note** As in the companion milestone, "the first $j$ routes" is the set $\{i : b_i < t\}$ and no ordering of the $b_i$ is assumed.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), p. 345, (1) Equal Times: "On the other hand, all of the first j routes must be in use"

import Mathlib
import Definitions.Def_WardropTraffic_EqualTimes_Setting

namespace WardropTraffic.EqualTimes

theorem lt_imp_used {D : ℕ} (b p : Fin D → ℝ) (hb : ∀ i, 0 < b i) (hp : ∀ i, 0 < p i)
    (Q t : ℝ) (q : Fin D → ℝ) (h : IsEqualTimes b p Q q t) :
    ∀ i, b i < t → 0 < q i := by sorry

end WardropTraffic.EqualTimes
