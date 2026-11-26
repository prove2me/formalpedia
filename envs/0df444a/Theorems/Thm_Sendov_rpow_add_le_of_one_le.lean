-- Prove2me | Theorems.Thm_Sendov_rpow_add_le_of_one_le
-- name    : Sendov.rpow_add_le_of_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:46:20.571932+00:00
-- url     : https://prove2.me/theorems/97074cf6-ecb2-5bab-a898-79a4a7ed9f21
-- title:
--   Sendov: rpow add le of one le
-- statement:
--   `(P+Q)^p ≤ P^p + p Q (P+Q)^(p-1)` for `p ≥ 1`.  This is the blog post's mean-value step,
--   obtained from Bernoulli's inequality after dividing by `(P+Q)^p`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Simplified.lean#L47-L67
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Simplified.lean#L47-L67

import Definitions.Def_Sendov_Reduction_Stat
import Definitions.Def_Sendov_Reduction_Simplified
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}

theorem Sendov.rpow_add_le_of_one_le {P Q p : ℝ} (hP : 0 ≤ P) (hPQ : 0 < P + Q) (hp : 1 ≤ p) :
    (P + Q) ^ p ≤ P ^ p + p * Q * (P + Q) ^ (p - 1) := by sorry
