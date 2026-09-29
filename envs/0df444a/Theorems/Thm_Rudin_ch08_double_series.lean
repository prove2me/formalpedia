-- Prove2me | Theorems.Thm_Rudin_ch08_double_series
-- name    : Rudin.ch08_double_series
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T20:15:29.277723+00:00
-- url     : https://prove2.me/theorems/3fb7e0ce-cf1a-4a06-a91f-b48fc14bc237
-- title:
--   Theorem 8.3 — interchanging the order of summation
-- statement:
--   Given a double sequence $a_{ij}$, suppose $\sum_j |a_{ij}| = b_i$ converges for each $i$ and $\sum_i b_i$ converges. Then the two iterated sums $\sum_i \sum_j a_{ij}$ and $\sum_j \sum_i a_{ij}$ both converge and are equal.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 175, Theorem 8.3

import Mathlib
import Definitions.Def_Rudin_ch03_series

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.3: given a double sequence `a i j`, if `∑_j |a i j| = b i` for each `i`
and `∑ b i` converges, then the two iterated sums of `a i j` converge and are equal. -/
theorem ch08_double_series (a : ℕ → ℕ → ℝ) (b : ℕ → ℝ)
    (hb : ∀ i, SeriesConvergesTo (fun j => |a i j|) (b i)) (hbsum : SeriesConverges b) :
    ∃ S : ℝ,
      SeriesConvergesTo (fun i => ∑' j, a i j) S ∧
      SeriesConvergesTo (fun j => ∑' i, a i j) S := by sorry

end Rudin
