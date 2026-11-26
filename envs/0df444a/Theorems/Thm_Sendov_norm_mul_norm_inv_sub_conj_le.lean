-- Prove2me | Theorems.Thm_Sendov_norm_mul_norm_inv_sub_conj_le
-- name    : Sendov.norm_mul_norm_inv_sub_conj_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:50:15.720877+00:00
-- url     : https://prove2.me/theorems/c3360724-6a37-4867-88fd-418de786784d
-- title:
--   Sendov: norm mul norm inv sub conj le
-- statement:
--   `‖w‖ · ‖w⁻¹ - conj w‖ ≤ 1 - ‖w‖²` for `‖w‖ ≤ 1`, with equality unless `w = 0`.  The
--   factor `‖w‖` on the left is what makes the origin harmless.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Defect.lean#L73-L88
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Defect.lean#L73-L88

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_Sendov_Analytic_Defect
set_option autoImplicit false
open Sendov
open Multiset

theorem Sendov.norm_mul_norm_inv_sub_conj_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖w‖ * ‖w⁻¹ - (starRingEnd ℂ) w‖ ≤ 1 - ‖w‖ ^ 2 := by sorry
