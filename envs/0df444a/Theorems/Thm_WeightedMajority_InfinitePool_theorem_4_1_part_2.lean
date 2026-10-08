-- Prove2me | Theorems.Thm_WeightedMajority_InfinitePool_theorem_4_1_part_2
-- name    : WeightedMajority.InfinitePool.theorem_4_1_part_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T14:57:32.3522+00:00
-- url     : https://prove2.me/theorems/347d47d9-63d3-4f63-a3d5-b0b73ad885fc
-- title:
--   Theorem 4.1(2) — total weight of WMI₂ after m mistakes is at most (2 − 1/(m+1)) u^m Ŵ(1)
-- statement:
--   Let $0 \le \beta < 1$, $u = (1+\beta)/2$, and let $W, \hat W$ be real functions on the positive integers with $W(i) > 0$ for all $i$, $\sum_i W(i) < \infty$, $\hat W(i) \ge \sum_{j \ge i} W(j)$ for all $i$, and $\hat W(i) \to 0$. Consider any run of $\mathrm{WMI}_2$ with parameter $\beta$ on any sequence of $T$ trials with binary predictions and labels. For $0 \le t \le T$ let $\omega_t(i)$ be the current weight of $A_i$ after the first $t$ trials if $A_i$ is active ($i \le l_t$), and $\omega_t(i) = W(i)$ if it is inactive.
--
--   If $m$ mistakes have been made by $\mathrm{WMI}_2$ in the first $t$ trials, then the series $\sum_i \omega_t(i)$ converges and
--   $$
--   \sum_{i=1}^{\infty} \omega_t(i) \le \Bigl(2 - \frac{1}{m+1}\Bigr)\, u^{m}\, \hat W(1).
--   $$
--
--   This is the potential bound behind the mistake bound of $\mathrm{WMI}_2$: every mistake shrinks the total weight, counting inactive members at their initial weights, by a factor close to $u$, the same factor as for the ordinary Weighted Majority Algorithm, at the price of the bounded overhead $2 - 1/(m+1) < 2$.
--
--   **Formalization Note.** The statement holds at every boundary $t \in \{0, \dots, T\}$ ("after any initial sequence of trials"). Summability is part of the conclusion so that the bound cannot hold through Lean's value $0$ for a divergent `tsum`. The paper's computability requirement on $W, \hat W$ is dropped; the result does not depend on it.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 227, Theorem 4.1, part 2

import Mathlib
import Definitions.Def_WeightedMajority_InfinitePool_IsWMI2Run

namespace WeightedMajority.InfinitePool

/-- Theorem 4.1, part 2 (Littlestone–Warmuth 1994, p. 227): after any initial sequence of
trials in which `m` mistakes have been made, `∑ ω_i ≤ (2 - 1/(m+1)) u^m Ŵ(1)`, where `ω_i` is
the current weight of an active member and `W(i)` for an inactive one. The family `ω` is also
asserted to be summable. -/
theorem theorem_4_1_part_2
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (W What : ℕ+ → ℝ) (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    (hWhat_lim : Filter.Tendsto What Filter.atTop (nhds 0))
    {T : ℕ} (x : Fin T → ℕ+ → Bool) (label : Fin T → Bool)
    (mi : ℕ+ → ℕ)
    (hmi : ∀ i, (Finset.univ.filter (fun t : Fin T => x t i ≠ label t)).card ≤ mi i)
    (prediction : Fin T → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ)
    (hrun : IsWMI2Run β W What x label prediction w l) :
    ∀ t ≤ T,
      Summable (omega W w l t) ∧
      ∑' i, omega W w l t i ≤
        (2 - 1 / ((mistakesBefore prediction label t : ℝ) + 1)) *
          u β ^ mistakesBefore prediction label t * What 1 := by sorry

end WeightedMajority.InfinitePool
