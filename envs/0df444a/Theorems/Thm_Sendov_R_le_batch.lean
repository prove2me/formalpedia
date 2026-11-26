-- Prove2me | Theorems.Thm_Sendov_R_le_batch
-- name    : Sendov.R_le_batch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:24.080708+00:00
-- url     : https://prove2.me/theorems/62435084-7bc3-422d-aa33-88c7b9cfb8db
-- title:
--   Sendov: R le batch
-- statement:
--   **The batch bound.**  One evaluation covers every degree in `[n₀, n₁]`: the elementary
--   part and the moment at `n₀`, the prefactor at `n₁`.
--
--   Only `0 ≤ c n₀ α` is required at `n₀`, not feasibility.  That matters: feasibility propagates
--   *upward* in `n`, so it could not be inherited from the hypothesis at `n`, and for `n₀ < 36` it
--   does not follow from `α ≤ 17` either.  Nonnegativity of `Q` at `n₀` instead comes free from
--   `Q_anti`, since `Q n₀ ≥ Q n ≥ 0`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L139-L190
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Batch.lean#L139-L190

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch
set_option autoImplicit false
open Sendov
variable {α t : ℝ}
open MeasureTheory

theorem Sendov.R_le_batch {n₀ n n₁ : ℕ} (h0 : 5 ≤ n₀) (h1 : n₀ ≤ n) (h2 : n ≤ n₁) (hα : 0 ≤ α)
    (hc0 : 0 ≤ c n₀ α) (hfn : c n α ^ 2 ≤ A n α) :
    R n α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n₀) + 1 / (4 * M n₀ * (3 + α))
      + A n₁ α ^ 2 * n₁ * M n₁ * ((n₁ : ℝ) - 2) / (4 * (3 + α))
        * ∫ t in (0 : ℝ)..1, t ^ 3 * Q n₀ α t ^ (((n₀ : ℝ) - 4) / 2) := by sorry
