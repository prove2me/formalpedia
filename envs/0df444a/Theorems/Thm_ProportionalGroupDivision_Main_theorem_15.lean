-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_theorem_15
-- name    : ProportionalGroupDivision.Main.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:10.653781+00:00
-- url     : https://prove2.me/theorems/2906509b-4474-4fbb-8658-c60a1867de20
-- title:
--   Theorem 15 (from Manurangsi–Meka) — a $0/1$ matrix with $\|A(v-\mathbf 1/k)\|_\infty\ge\sqrt{r-1}/16$ for every $v\in\{0,1\}^{rk}$
-- statement:
--   For all integers $r\ge1$ and $k\ge2$ there is a matrix $A\in\{0,1\}^{r\times m}$ with $m=r\cdot k$ such that every $v\in\{0,1\}^m$ satisfies
--
--   $$\big\|A\,(v-\mathbf 1/k)\big\|_\infty\ \ge\ \frac{\sqrt{r-1}}{16}.$$
--
--   The matrix is chosen before $v$, and $v$ ranges over all binary vectors (not only partitions). It is the weighted-discrepancy obstruction behind the lower bound of Theorem 4.
--
--   Differences from the source:
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
--   - encoding: ‖A(v − 1/k)‖_∞ ≥ √(r−1)/16 → some row i has |Σ_g A_{i,g}(v_g − 1/k)| ≥ √(r−1)/16; 0/1 entries as real numbers; reason: r ≥ 1 rows, so the maximum is attained by a row
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Theorem 15 (consequence of Theorem 3.2 of Manurangsi–Meka [MM26]), PDF p. 15 = printed p. 15

import Mathlib

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-- Theorem 15 (consequence of Theorem 3.2 of Manurangsi–Meka [MM26], PDF p. 15): for all integers
`r ≥ 1` and `k ≥ 2` there is a matrix `A ∈ {0,1}^{r×m}` with `m = r · k` such that every
`v ∈ {0,1}^m` has `‖A(v − 𝟙/k)‖_∞ ≥ √(r − 1)/16`, i.e. some row `i` has
`|∑_g A_{i,g} (v_g − 1/k)| ≥ √(r − 1)/16`. -/
theorem theorem_15 (r k : ℕ) (hr : 1 ≤ r) (hk : 2 ≤ k) :
    ∃ A : Matrix (Fin r) (Fin (r * k)) ℝ, (∀ i g, A i g = 0 ∨ A i g = 1) ∧
      ∀ v : Fin (r * k) → ℝ, (∀ g, v g = 0 ∨ v g = 1) →
        ∃ i : Fin r, Real.sqrt ((r : ℝ) - 1) / 16 ≤ |∑ g, A i g * (v g - 1 / (k : ℝ))| := by sorry

end ProportionalGroupDivision.Main
