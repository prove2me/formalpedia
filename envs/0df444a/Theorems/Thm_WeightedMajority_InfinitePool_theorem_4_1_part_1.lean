-- Prove2me | Theorems.Thm_WeightedMajority_InfinitePool_theorem_4_1_part_1
-- name    : WeightedMajority.InfinitePool.theorem_4_1_part_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:57:09.051142+00:00
-- url     : https://prove2.me/theorems/3458573d-f52e-4019-903f-c816a3ab685a
-- title:
--   Theorem 4.1(1) — size of the active pool of WMI₂
-- statement:
--   Let $0 \le \beta < 1$, $u = (1+\beta)/2$, and let $W, \hat W$ be real functions on the positive integers with $W(i) > 0$ for all $i$, $\sum_i W(i) < \infty$, $\hat W(i) \ge \sum_{j \ge i} W(j)$ for all $i$, and $\hat W(i) \to 0$. Let $x_t(i)$, $\rho_t$ ($t = 0, \dots, T-1$) be any sequence of predictions of the pool members $A_1, A_2, \dots$ and labels, on which $A_i$ makes at most $m_i$ mistakes, and consider any run of $\mathrm{WMI}_2$ with parameter $\beta$ on it.
--
--   Then at the beginning of every trial $t$ the size $l_t$ of the active pool is the minimum $l$ such that
--   $$
--   \hat W(l+1) \le \frac{u^{m+1}\,\hat W(1)}{(1-\beta)(m+1)(m+2)},
--   $$
--   where $m$ is the number of mistakes made by $\mathrm{WMI}_2$ in the trials before $t$.
--
--   The algorithm raises $l$ to the least admissible value at or above its previous value; this statement says that this local rule yields the global minimum, so the active pool is no larger than necessary. Part 1 is used in the proof of part 2 to bound the total weight of the inactive members.
--
--   **Formalization Note.** Minimality is stated as: the inequality holds at $l_t$ and fails at every $l' < l_t$. The pool is indexed by `ℕ+`, so $\hat W(l+1)$ is `What (Nat.succPNat l)`. The hypotheses on $W, \hat W$ are those of Theorem 4.1, without the paper's computability requirement, which the result does not depend on.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 226, Theorem 4.1, part 1

import Mathlib
import Definitions.Def_WeightedMajority_InfinitePool_IsWMI2Run

namespace WeightedMajority.InfinitePool

/-- Theorem 4.1, part 1 (Littlestone–Warmuth 1994, p. 226): at the beginning of any trial the
size of the active pool of WMI₂ is the minimum `l` with `Ŵ(l + 1) ≤ slack m`, where `m` is the
number of mistakes made in prior trials. -/
theorem theorem_4_1_part_1
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (W What : ℕ+ → ℝ) (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    (hWhat_lim : Filter.Tendsto What Filter.atTop (nhds 0))
    {T : ℕ} (x : Fin T → ℕ+ → Bool) (label : Fin T → Bool)
    (mi : ℕ+ → ℕ)
    (hmi : ∀ i, (Finset.univ.filter (fun t : Fin T => x t i ≠ label t)).card ≤ mi i)
    (prediction : Fin T → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ)
    (hrun : IsWMI2Run β W What x label prediction w l) :
    ∀ t : Fin T,
      What (Nat.succPNat (l t.val)) ≤ slack β What (mistakesBefore prediction label t.val) ∧
      ∀ l' < l t.val,
        slack β What (mistakesBefore prediction label t.val) < What (Nat.succPNat l') := by sorry

end WeightedMajority.InfinitePool
