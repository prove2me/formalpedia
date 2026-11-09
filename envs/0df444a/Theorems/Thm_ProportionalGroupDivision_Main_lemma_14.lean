-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_lemma_14
-- name    : ProportionalGroupDivision.Main.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:52.99535+00:00
-- url     : https://prove2.me/theorems/2c091a17-cf35-46ed-92f3-1e74a9b9a0cc
-- title:
--   Lemma 14 — $\mathrm{disc}^k_>(n_1,\dots,n_k)\ge(k-1)/k$
-- statement:
--   For every $k\ge2$ and positive integers $n_1\ge\dots\ge n_k$,
--
--   $$\mathrm{disc}^k_>(n_1,\dots,n_k)\ \ge\ \frac{k-1}{k}.$$
--
--   This handles the regime of small $n/k$ in the lower bound of Theorem 4.
--
--   Differences from the source:
--   - encoding: disc^k_>(n_1, …, n_k) as a real maximum → the ℝ≥0∞ supremum over m ≥ 1 and matrices of the minimum over partitions of the largest shortfall truncated at 0; reason: zero matrices have value 0, so the truncation changes no worst-case value; an extended supremum has no junk default
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Lemma 14, PDF p. 15 = printed p. 15

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Discrepancy

namespace ProportionalGroupDivision.Main

/-- Lemma 14 (PDF p. 15): for `k ≥ 2` and positive group sizes `n_1 ≥ ⋯ ≥ n_k ≥ 1`,
`disc^k_>(n_1, …, n_k) ≥ (k − 1)/k`. -/
theorem lemma_14 (k : ℕ) (hk : 2 ≤ k) (n : Fin k → ℕ) (hmono : Antitone n)
    (hpos : ∀ i, 0 < n i) :
    ENNReal.ofReal (((k : ℝ) - 1) / k) ≤ discOne n := by sorry

end ProportionalGroupDivision.Main
