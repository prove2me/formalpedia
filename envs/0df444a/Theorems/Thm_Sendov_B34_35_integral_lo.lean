-- Prove2me | Theorems.Thm_Sendov_B34_35_integral_lo
-- name    : Sendov.B34_35.integral_lo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:14:38.098129+00:00
-- url     : https://prove2.me/theorems/df59adc1-9ec2-4794-925d-0073610c8114
-- title:
--   B34 35: integral lo
-- statement:
--   The B34 35 construction uses the integral lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree34_35.lean#L79-L83
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree34_35.lean#L79-L83

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree34_35
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B34_35

theorem Sendov.B34_35.integral_lo (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q 34 α t ^ 15)
      = pev Nmomc α / ((Lc : ℝ) * (2 * M 34 * (3 + α)) ^ 15) := by sorry
