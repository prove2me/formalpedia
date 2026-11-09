-- Prove2me | Theorems.Thm_ProportionalGroupDivision_Main_lemma_3
-- name    : ProportionalGroupDivision.Main.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:04.15054+00:00
-- url     : https://prove2.me/theorems/a10f23bc-7898-4150-964e-09047599a10b
-- title:
--   Lemma 3 — $\mathrm{disc}^k_>(n_1,\dots,n_k)\le\mathrm{PROP}(n_1,\dots,n_k)\le2\lceil\mathrm{disc}^k_>(n_1,\dots,n_k)\rceil$
-- statement:
--   For every $k\ge2$ and $n_1\ge\dots\ge n_k\ge1$,
--
--   $$\mathrm{disc}^k_>(n_1,\dots,n_k)\ \le\ \mathrm{PROP}(n_1,\dots,n_k)\ \le\ 2\cdot\big\lceil\mathrm{disc}^k_>(n_1,\dots,n_k)\big\rceil .$$
--
--   Both inequalities are asserted without assuming either side finite. The lemma transfers bounds between the fair-division quantity and the one-sided discrepancy quantity.
--
--   Differences from the source:
--   - encoding: disc^k_>(n_1, …, n_k) as a real maximum → the ℝ≥0∞ supremum over m ≥ 1 and matrices of the minimum over partitions of the largest shortfall truncated at 0; reason: zero matrices have value 0, so the truncation changes no worst-case value; an extended supremum has no junk default
--   - encoding: PROP(n_1, …, n_k) the smallest positive integer, ⌈·⌉ the integer ceiling → PROP in ℕ∞ (∞ if no integer works) compared in ℝ≥0∞; ⌈·⌉ on ℝ≥0∞ with ⌈∞⌉ = ∞; reason: the same values whenever the quantities are finite, with no junk value otherwise
--   - encoding: rows, agents and goods indexed 1, …, n → 0-based indices Fin n; agent (i, j) is a dependent pair with j : Fin (n i); reason: relabelling; changes no instance
-- source:
--   Alexander Shekhovtsov, Georgy Sokolov, Mikhail Cherniavskii, Andrey Kupavskii, Nearly Tight Bounds for Proportional Group Fair Divisions and One-Sided Discrepancy, STOC 2027 submission #606 (October 2026), PDF SHA-256 b01bf42964a30eaf9c85a3d02713fc0ac4cd63ae8653853fa44b062c0220f39a, Lemma 3, PDF p. 4 = printed p. 4; proof in Appendix A, PDF pp. 22–25

import Mathlib
import Definitions.Def_ProportionalGroupDivision_Main_Model
import Definitions.Def_ProportionalGroupDivision_Main_Discrepancy

open scoped ENNReal

namespace ProportionalGroupDivision.Main

/-- Lemma 3 (PDF p. 4; proof in Appendix A, pp. 22–25): for every `k ≥ 2` and
`n_1 ≥ ⋯ ≥ n_k ≥ 1`, `disc^k_>(n_1, …, n_k) ≤ PROP(n_1, …, n_k) ≤ 2 · ⌈disc^k_>(n_1, …, n_k)⌉`. -/
theorem lemma_3 (k : ℕ) (hk : 2 ≤ k) (n : Fin k → ℕ) (hmono : Antitone n)
    (hpos : ∀ i, 0 < n i) :
    discOne n ≤ ((PROP n : ℕ∞) : ℝ≥0∞) ∧ PROP n ≤ 2 * ceilE (discOne n) := by sorry

end ProportionalGroupDivision.Main
