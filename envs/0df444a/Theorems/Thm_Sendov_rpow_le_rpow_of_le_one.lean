-- Prove2me | Theorems.Thm_Sendov_rpow_le_rpow_of_le_one
-- name    : Sendov.rpow_le_rpow_of_le_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:56:24.333797+00:00
-- url     : https://prove2.me/theorems/e538fe3d-c74f-53ed-832b-094d2f1bc32e
-- title:
--   Sendov: rpow le rpow of le one
-- statement:
--   On `[0,1]` a real power is decreasing in the exponent: `x ^ s ≤ x ^ t` for `t ≤ s`.
--   Used to drop the `√B` from `B ^ (k + 1/2)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Rpow.lean#L58-L60
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Rpow.lean#L58-L60

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_Common_Rpow
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.rpow_le_rpow_of_le_one {x s t : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hts : t ≤ s) :
    x ^ s ≤ x ^ t := by sorry
