-- Prove2me | Theorems.Thm_WagelmansELS_DualGreedy_equation_2
-- name    : WagelmansELS.DualGreedy.equation_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:02:06.040736+00:00
-- url     : https://prove2.me/theorems/aaad52a0-32f2-4e2c-8779-b6da78a04d01
-- title:
--   Equation (2) — greedy prefix value at a minimizing period
-- statement:
--   Fix a positive-demand period $j$ and an index $1\le k\le j$ attaining the minimum in the greedy formula for $v_j$. Assume the induction hypothesis that the greedy prefix value through $k-1$ is $F(k-1)$. Then
--
--   $$\sum_{t=1}^{j}d_tv_t=f_k+c_kd_{k,j}+F(k-1).$$
--
--   This is Equation (2) of the paper. The minimizing-index equality and the induction hypothesis are explicit assumptions; the monotonicity needed in its derivation remains a conclusion of the separate milestone.
-- source:
--   Wagelmans, Van Hoesel and Kolen, Economic Lot Sizing, Oper. Res. 40 Supp. 1 (1992), p. S153, Eq. (2) and the preceding sentence

import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Greedy

namespace WagelmansELS.DualGreedy

theorem equation_2 (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v)
    (j k : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ P.n) (hdj : 0 < P.d j)
    (hk1 : 1 ≤ k) (hkj : k ≤ j)
    (hk : v j = greedyBound P v k j)
    (hind : objective P v (k - 1) = F P (k - 1)) :
    objective P v j = P.f k + P.c k * demand P k j + F P (k - 1) := by sorry

end WagelmansELS.DualGreedy
