-- Prove2me | Theorems.Thm_Sendov_norm_prod_map
-- name    : Sendov.norm_prod_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:53:25.084846+00:00
-- url     : https://prove2.me/theorems/a5a8e2cb-5ba9-4ca0-a6de-703f379de3b5
-- title:
--   Sendov: norm prod map
-- statement:
--   Norms distribute over a mapped multiset product.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L98-L101
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L98-L101

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory

theorem Sendov.norm_prod_map (s : Multiset ℂ) (f : ℂ → ℂ) :
    ‖(s.map f).prod‖ = (s.map (fun w => ‖f w‖)).prod := by sorry
