-- Prove2me | Theorems.Thm_Sendov_rotate_rotate_inv
-- name    : Sendov.rotate_rotate_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:06:03.832248+00:00
-- url     : https://prove2.me/theorems/bc5345e9-6109-5256-8cae-84e0265a2332
-- title:
--   Sendov: rotate rotate inv
-- statement:
--   Rotating is undone by rotating back.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L63-L66
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L63-L66

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
import Definitions.Def_Sendov_Conjecture
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.rotate_rotate_inv {ω : ℂ} (hω : ω ≠ 0) (p : ℂ[X]) : rotate ω⁻¹ (rotate ω p) = p := by sorry
