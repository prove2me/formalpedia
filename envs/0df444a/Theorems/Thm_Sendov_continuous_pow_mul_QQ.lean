-- Prove2me | Theorems.Thm_Sendov_continuous_pow_mul_QQ
-- name    : Sendov.continuous_pow_mul_QQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:10.060803+00:00
-- url     : https://prove2.me/theorems/ad1aaaca-e664-537c-8e66-8749db13435b
-- title:
--   Sendov: continuous pow mul QQ
-- statement:
--   `t ^ k * QQ ^ e` is continuous, hence interval integrable: needed wherever an integral of
--   this shape is split or compared.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L85-L89
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L85-L89

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic
set_option autoImplicit false
open Sendov
variable {c A t : ℝ}

theorem Sendov.continuous_pow_mul_QQ (c A : ℝ) (k : ℕ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ k * QQ c A t ^ e := by sorry
