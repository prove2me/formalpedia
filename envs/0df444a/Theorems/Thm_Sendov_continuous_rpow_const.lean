-- Prove2me | Theorems.Thm_Sendov_continuous_rpow_const
-- name    : Sendov.continuous_rpow_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:53:49.958729+00:00
-- url     : https://prove2.me/theorems/80ce263c-1eb1-58c4-8cd2-fed62cd17294
-- title:
--   Sendov: continuous rpow const
-- statement:
--   `fun x ↦ x ^ e` is continuous on all of `ℝ` for a nonnegative real exponent `e`.  The
--   exponent must be nonnegative: at `e < 0` the function blows up at the origin.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Rpow.lean#L44-L45
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Rpow.lean#L44-L45

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_Common_Rpow
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.continuous_rpow_const {e : ℝ} (he : 0 ≤ e) : Continuous fun x : ℝ => x ^ e := by sorry
