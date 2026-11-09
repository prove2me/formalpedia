-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_lemma_16
-- name    : ProportionalGroupDivision.Main.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:14.081194+00:00
-- url     : https://prove2.me/theorems/756737c2-e212-4791-ad49-048ced4747af
-- title:
--   Lemma 16 — complementary rows turn a two-sided deviation into a one-sided shortfall
-- statement:
--   For integers $r\ge1$ and $k\ge2$ there is $m_0$ such that for every $m\ge m_0$ there is a matrix $B\in\{0,1\}^{2r\times m}$ with the following property: for every $v\in\{0,1\}^m$ there is a row $i$ with
--
--   $$\langle B_i,v\rangle\ \le\ \langle B_i,\mathbf 1/k\rangle-\frac{\sqrt{r-1}}{16}+\max\big(0,\ \|v\|_1-m/k\big). \tag{5}$$
--
--   The matrix $B$ is chosen before $v$. It is the block used in the construction of Section 3.1.
--
--   Differences from the source:
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Lemma 16, PDF p. 16 = printed p. 16

import Mathlib

open scoped BigOperators

namespace ProportionalGroupDivision.Main

/-- Lemma 16 (PDF p. 16): for integers `r ≥ 1` and `k ≥ 2` there is `m₀` such that for every
`m ≥ m₀` there is a matrix `B ∈ {0,1}^{2r×m}` with the following property: for every
`v ∈ {0,1}^m` some row `i` satisfies
`⟨B_i, v⟩ ≤ ⟨B_i, 𝟙/k⟩ − √(r − 1)/16 + max(0, ‖v‖₁ − m/k)` (5). -/
theorem lemma_16 (r k : ℕ) (hr : 1 ≤ r) (hk : 2 ≤ k) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ B : Matrix (Fin (2 * r)) (Fin m) ℝ, (∀ i g, B i g = 0 ∨ B i g = 1) ∧
        ∀ v : Fin m → ℝ, (∀ g, v g = 0 ∨ v g = 1) →
          ∃ i : Fin (2 * r),
            ∑ g, B i g * v g ≤
              ∑ g, B i g * (1 / (k : ℝ)) - Real.sqrt ((r : ℝ) - 1) / 16 +
                max 0 (∑ g, v g - (m : ℝ) / k) := by sorry

end ProportionalGroupDivision.Main
