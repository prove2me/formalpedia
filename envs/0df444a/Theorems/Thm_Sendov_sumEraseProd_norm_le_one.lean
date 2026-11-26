-- Prove2me | Theorems.Thm_Sendov_sumEraseProd_norm_le_one
-- name    : Sendov.sumEraseProd_norm_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:54:52.375803+00:00
-- url     : https://prove2.me/theorems/29a787c0-b0ef-5343-bc74-f01cbc0f1da3
-- title:
--   Sendov: sum Erase Prod norm le one
-- statement:
--   The degenerate case.  If `∏ sⱼ = 0` then some `sⱼ` vanishes, so at most one term of
--   `∑ⱼ ∏_{k≠j} sₖ` is nonzero — and that term is a product of points of the closed unit disk.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L97-L116
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L97-L116

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
set_option autoImplicit false
open Sendov

theorem Sendov.sumEraseProd_norm_le_one : ∀ (s : Multiset ℂ), (∀ w ∈ s, ‖w‖ ≤ 1) → s.prod = 0 →
    ‖sumEraseProd s‖ ≤ 1 := by sorry
