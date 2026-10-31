-- Prove2me | Theorems.Thm_SinkhornHall_step2_output_exists
-- name    : SinkhornHall.step2_output_exists
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:40.578874+00:00
-- url     : https://prove2.me/theorems/d192ca75-014b-4f00-8a0d-3cb2e5b12c98
-- title:
--   Algorithm step 2 — an admissible $k^*$ exists
-- statement:
--   Let $n\ge1$ and let $x,y\in\mathbb R^n$ be positive vectors. Sort $x_{i_1}\ge\dots\ge x_{i_n}$ and $y_{j_1}\le\dots\le y_{j_n}$. Then there is an index $k^*$ with
--
--   $$(x_{i_{k^*}}y_{j_{k^*}})^n\ \ge\ x_1\cdots x_n\,y_1\cdots y_n,$$
--
--   so step 2 of the algorithm "Sinkhorn & Sorting Scaling Vectors" always produces an output $\{i_1,\dots,i_{k^*}\}$.
--
--   The paper takes this for granted when it says "Choose index $k^*$"; stating it makes the goal theorem's conclusion non-vacuous.
--
--   Differences from the source:
--   - reading: 'Choose index k* such that …' (existence presupposed) → ∃ X, IsStep2Output x y X for positive x, y and n ≥ 1; reason: the instruction is only meaningful if such k* exists; the claim is what the step presupposes
--   - encoding: 1-based indices i_1, …, i_n and k* ∈ {1, …, n} → Fin n (0-based), i_t = σ (t − 1), k = k* − 1, output σ '' {0, …, k}; reason: Lean convention; the output has k* elements as in the paper
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, §4.1, Algorithm: Sinkhorn & Sorting Scaling Vectors, step 2, p.15

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis

open Finset

namespace SinkhornHall

/-- **Step 2 of the algorithm is well posed: an admissible `k*` exists.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §4.1, Algorithm: Sinkhorn & Sorting Scaling Vectors,
step 2, p.15: "Sort x, y as x_{i₁} ≥ ⋯ ≥ x_{iₙ}, y_{j₁} ≤ ⋯ ≤ y_{jₙ}. Choose index k* such that
(x_{i_{k*}} y_{j_{k*}})ⁿ ≥ x₁x₂⋯xₙy₁y₂⋯yₙ. Output {i₁, …, i_{k*}}."

For positive scaling vectors `x`, `y` with `n ≥ 1`, some output of step 2 exists.

**Formalization Note.** `IsStep2Output x y X` records every admissible choice of sorts and `k*`;
the claim is that the relation is satisfiable. -/
theorem step2_output_exists {n : ℕ} (hn : 0 < n) (x y : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (hy : ∀ j, 0 < y j) :
    ∃ X : Finset (Fin n), IsStep2Output x y X := by sorry

end SinkhornHall
