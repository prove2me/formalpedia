-- Prove2me | Theorems.Thm_Sendov_collapse_J
-- name    : Sendov.collapse_J
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:58:08.204875+00:00
-- url     : https://prove2.me/theorems/923b2de3-5e5a-41b3-b719-06211cd93689
-- title:
--   Sendov: collapse J
-- statement:
--   Replacing `|J|` by `1`: `P K + c(1 - P²) ≤ K` on `0 ≤ P ≤ 1` once `K ≥ 2c ≥ 0`, since
--   `K - P K - c(1-P²) = (1-P)(K - c(1+P))`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L109-L114
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/OriginExact.lean#L109-L114

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
set_option autoImplicit false
open Sendov
open Complex (I)

theorem Sendov.collapse_J {K c P : ℝ} (hP1 : P ≤ 1) (hc0 : 0 ≤ c) (hcK : 2 * c ≤ K) :
    P * K + c * (1 - P ^ 2) ≤ K := by sorry
