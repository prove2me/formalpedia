-- Prove2me | Theorems.Thm_Sendov_integral_le_tail_gen
-- name    : Sendov.integral_le_tail_gen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:19.042435+00:00
-- url     : https://prove2.me/theorems/692f11b7-8731-5ba4-818d-56001335a5c8
-- title:
--   Sendov: integral le tail gen
-- statement:
--   **The tail bound, for an arbitrary weight `t^k`.**  `QQ` is a convex parabola with vertex
--   at `c/A`; below the vertex it lies under the chord `1 - ct`, above it it is increasing and so
--   at most `QQ 1`.  Splitting `∫₀¹` there gives the bound.
--
--   Two points shape the proof.  The chord bound needs `1 - ct ≥ 0`, which comes from
--   `ct ≤ c²/A ≤ 1` — feasibility again.  And the vertex may lie outside `[0,1]`: the split is
--   made at `s = min (c/A) 1`, after which the first piece is enlarged to `[0, 1/c]` (legitimate
--   because `s ≤ 1/c`, using `c ≤ 1` when the vertex is to the right) and the second piece is
--   empty when the vertex is beyond `1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L176-L253
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Chord.lean#L176-L253

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.integral_le_tail_gen {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ c A t ^ r)
      ≤ (∫ t in (0 : ℝ)..1 / c, t ^ k * (1 - c * t) ^ r) + QQ c A 1 ^ r / (k + 1) := by sorry
