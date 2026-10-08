-- Prove2me | Theorems.Thm_WeightedMajority_InfinitePool_theorem_4_1_part_3
-- name    : WeightedMajority.InfinitePool.theorem_4_1_part_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:57:22.112063+00:00
-- url     : https://prove2.me/theorems/69fc207c-954a-4883-b01c-ea15814fdaee
-- title:
--   Theorem 4.1(3) — WMI₂ makes at most inf_i (log(Ŵ(1)/W(i)) + m_i log(1/β) + log 2)/log(1/u) mistakes
-- statement:
--   Let $0 \le \beta < 1$ and $u = (1+\beta)/2$. Let $W, \hat W$ be real functions on the positive integers with $W(i) > 0$ for all $i$, $\sum_i W(i) < \infty$, $\hat W(i) \ge \sum_{j \ge i} W(j)$ for all $i$, and $\lim_{i\to\infty} \hat W(i) = 0$. Let $x_t(i), \rho_t$ ($t = 0, \dots, T-1$) be any finite sequence of binary predictions of a countably infinite pool $A_1, A_2, \dots$ and binary labels, on which $A_i$ makes at most $m_i$ mistakes, for every $i \ge 1$. Let $m$ be the total number of mistakes of any run of $\mathrm{WMI}_2$ with parameter $\beta$ on this sequence.
--
--   1. If $0 < \beta < 1$, then
--   $$
--   m \le \inf_{i \ge 1} \frac{\log\bigl(\hat W(1)/W(i)\bigr) + m_i \log(1/\beta) + \log 2}{\log(1/u)}.
--   $$
--   2. If $\beta = 0$ and $m_i = 0$ for some $i$, then $m \le 1 + \log_2\bigl(\hat W(1)/W(i)\bigr)$.
--
--   This is the main result of Section 4: on an infinite pool, with only a finite active subpool maintained at any time, $\mathrm{WMI}_2$ achieves essentially the bound that the (infeasible) Weighted Majority Algorithm on all infinitely many weights would give, up to the additive $\log 2$ in the numerator. Choosing $W$ and $\hat W$ trades the mistake bound against the growth of the active pool.
--
--   **Formalization Note.** The infimum over $i$ is stated as the bound for every $i$, which is equivalent. In case 1 the logarithms appear in a ratio, so their base is irrelevant (as the paper notes); the natural logarithm is used. Case 2 uses the base-2 logarithm, as printed. All logarithms are of positive numbers under the hypotheses ($\hat W(1) \ge W(i) > 0$, $0 < u < 1$). The paper's computability requirement on $W, \hat W$ is dropped: the result does not depend on it, so the statement is a generalization.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 227, Theorem 4.1, part 3

import Mathlib
import Definitions.Def_WeightedMajority_InfinitePool_IsWMI2Run

namespace WeightedMajority.InfinitePool

/-- Theorem 4.1, part 3 (Littlestone–Warmuth 1994, p. 227). If `0 < β < 1`, the total number
`m` of mistakes of WMI₂ is at most `(log(Ŵ(1)/W(i)) + m_i log(1/β) + log 2) / log(1/u)` for every
`i` (equivalently, at most the infimum over `i ≥ 1`). If `β = 0` and `m_i = 0` for some `i`, then
`m ≤ 1 + log₂(Ŵ(1)/W(i))`. -/
theorem theorem_4_1_part_3
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (W What : ℕ+ → ℝ) (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    (hWhat_lim : Filter.Tendsto What Filter.atTop (nhds 0))
    {T : ℕ} (x : Fin T → ℕ+ → Bool) (label : Fin T → Bool)
    (mi : ℕ+ → ℕ)
    (hmi : ∀ i, (Finset.univ.filter (fun t : Fin T => x t i ≠ label t)).card ≤ mi i)
    (prediction : Fin T → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ)
    (hrun : IsWMI2Run β W What x label prediction w l) :
    (0 < β → ∀ i : ℕ+,
      (mistakesBefore prediction label T : ℝ) ≤
        (Real.log (What 1 / W i) + (mi i : ℝ) * Real.log (1 / β) + Real.log 2) /
          Real.log (1 / u β)) ∧
    (β = 0 → ∀ i : ℕ+, mi i = 0 →
      (mistakesBefore prediction label T : ℝ) ≤ 1 + Real.logb 2 (What 1 / W i)) := by sorry

end WeightedMajority.InfinitePool
