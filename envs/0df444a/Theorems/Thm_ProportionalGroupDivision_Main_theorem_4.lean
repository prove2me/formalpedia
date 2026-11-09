-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_theorem_4
-- name    : ProportionalGroupDivision.Main.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:54.153371+00:00
-- url     : https://prove2.me/theorems/b1a39491-25a7-48a9-b05d-4f986e61efba
-- title:
--   Theorem 4 — $\mathrm{disc}^k_>(n_1,\dots,n_k)$ is between $\Omega(\sqrt{n/k})$ and $O(\sqrt{(n/k)(\ln^3(n_1k/n)+1)})$
-- statement:
--   There are absolute constants $a,b>0$ such that for every $k\ge2$ and all positive integers $n_1\ge\dots\ge n_k$, with $n=n_1+\dots+n_k$,
--
--   $$a\sqrt{\frac nk}\ \le\ \mathrm{disc}^k_>(n_1,\dots,n_k)\ \le\ b\sqrt{\frac nk\cdot\Big(\ln^3\Big(\frac{n_1k}{n}\Big)+1\Big)} .$$
--
--   In particular the worst-case one-sided discrepancy is finite. By Lemma 3 this is equivalent to the bounds of Theorem 2.
--
--   Differences from the source:
--   - encoding: Ω(·) and O(·) → explicit constants a, b > 0 chosen before k and the group sizes; reason: the meaning of the asymptotic notation, uniform in all parameters
--   - encoding: disc^k_>(n_1, …, n_k) as a real maximum → the ℝ≥0∞ supremum over m ≥ 1 and matrices of the minimum over partitions of the largest shortfall truncated at 0; reason: zero matrices have value 0, so the truncation changes no worst-case value; an extended supremum has no junk default
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Theorem 4, PDF p. 4 = printed p. 4; upper bound proved in Section 2, PDF pp. 7–15; lower bound in Section 3, PDF pp. 15–18

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Discrepancy

open scoped BigOperators ENNReal

namespace ProportionalGroupDivision.Main

/-- Theorem 4 (PDF p. 4): there are absolute constants `a, b > 0` such that for every `k ≥ 2` and
all positive integers `n_1 ≥ ⋯ ≥ n_k`, with `n = n_1 + ⋯ + n_k`,
`a √(n/k) ≤ disc^k_>(n_1, …, n_k) ≤ b √((n/k) · (ln³(n_1 · k/n) + 1))`. -/
theorem theorem_4 :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ (k : ℕ) (hk : 2 ≤ k) (n : Fin k → ℕ), Antitone n → (∀ i, 0 < n i) →
        ENNReal.ofReal (a * Real.sqrt ((∑ i, (n i : ℝ)) / k)) ≤ discOne n ∧
        discOne n ≤ ENNReal.ofReal (b * Real.sqrt ((∑ i, (n i : ℝ)) / k *
          (Real.log ((n ⟨0, by omega⟩ : ℝ) * k / ∑ i, (n i : ℝ)) ^ 3 + 1))) := by sorry

end ProportionalGroupDivision.Main
