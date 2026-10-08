-- Prove2me | Theorems.Thm_WagelmansELS_DualGreedy_greedy_forward_monotone
-- name    : WagelmansELS.DualGreedy.greedy_forward_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:57:54.458242+00:00
-- url     : https://prove2.me/theorems/a7dc2af5-bb74-4652-8bef-4e8c014c7ae8
-- title:
--   Section 4 — greedy dual values decrease across positive demands
-- statement:
--   Let $v$ satisfy the greedy forward rule with nonnegative demands and setup costs. For any positive-demand periods $1\le t<j\le n$,
--
--   $$v_j\le v_t.$$
--
--   The paper states the result first for consecutive periods with nonzero demand, then observes that the dual values at zero-demand periods can be assigned freely. The formal statement skips those periods, so it holds for every allowed assignment of their values.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), p. S153, Section 4, “if d_j ≠ 0 and d_{j+1} ≠ 0, then v_j ≥ v_{j+1}” and the following zero-demand sentence

import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Greedy

namespace WagelmansELS.DualGreedy

theorem greedy_forward_monotone (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v)
    (t j : ℕ) (ht : 1 ≤ t) (htj : t < j) (hjn : j ≤ P.n)
    (hdt : 0 < P.d t) (hdj : 0 < P.d j) : v j ≤ v t := by sorry

end WagelmansELS.DualGreedy
