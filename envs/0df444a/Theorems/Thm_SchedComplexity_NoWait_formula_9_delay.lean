-- Prove2me | Theorems.Thm_SchedComplexity_NoWait_formula_9_delay
-- name    : SchedComplexity.NoWait.formula_9_delay
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:02:22.890336+00:00
-- url     : https://prove2.me/theorems/e4e54d83-7e75-4f6e-8235-cde019efae50
-- title:
--   Formula (9) — c_jk = max_{1≤i≤m} {q_ji − q_{k,i−1}} is the least gap between B_j and B_k
-- statement:
--   Consider a no-wait flow shop with $n$ jobs, $m\ge1$ machines and processing times $p_{\ell i}\in\mathbb N$, and let $q_{\ell i}=\sum_{r\le i}p_{\ell r}$ as in (8). For two distinct jobs $J_j$ and $J_k$, the paper defines $c_{jk}$ as "the minimum length of the time interval between $B_j$ and $B_k$ if $J_k$ is scheduled directly after $J_j$", and states (9):
--   $$c_{jk}=\max_{1\le i\le m}\{q_{ji}-q_{k,i-1}\}.$$
--   Precisely: among all $\delta\ge0$ such that, with $B_k=B_j+\delta$, the operation of $J_j$ on every machine $M_i$ ends no later than the operation of $J_k$ on $M_i$ starts, i.e.
--   $$q_{ji}\le\delta+q_{k,i-1}\qquad(i=1,\dots,m),$$
--   the least is $\max_{1\le i\le m}\{q_{ji}-q_{k,i-1}\}$.
--
--   This is the weight of the arc $(j,k)$ in the travelling-salesman reformulation of no-wait scheduling.
--
--   **Formalization Note** "$J_k$ is scheduled directly after $J_j$" is read as "$J_j$ precedes $J_k$ on every machine", the only constraint between the two jobs; no other job intervenes in this statement. The gap $\delta$ ranges over the nonnegative integers (as elements of $\mathbb Z$).
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 24, Eqs. (8)–(9)

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_NoWaitFlowShop

namespace SchedComplexity.NoWait

/-- Formula (9), p. 24: if job `k` is scheduled directly after job `j` (read: `B_k = B_j + δ`
with `δ ≥ 0`, and on every machine the operation of `j` ends before the operation of `k`
starts), the least admissible `δ` is `c_{jk} = max_{1 ≤ i ≤ m} {q_{j i} − q_{k,i−1}}`. -/
theorem formula_9_delay {n m : ℕ} (p : Fin n → Fin m → ℕ) (hm : 0 < m) (j k : Fin n)
    (hjk : j ≠ k) :
    IsLeast {δ : ℤ | 0 ≤ δ ∧ ∀ r : Fin m, (cum p j (r.val + 1) : ℤ) ≤ δ + (cum p k r.val : ℤ)}
      (delay p hm j k) := by sorry

end SchedComplexity.NoWait
