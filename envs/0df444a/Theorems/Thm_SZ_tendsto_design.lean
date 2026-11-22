-- Prove2me | Theorems.Thm_SZ_tendsto_design
-- name    : SZ.tendsto_design
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:52:19.553953+00:00
-- url     : https://prove2.me/theorems/2199e8bd-46d1-4509-926d-096feb6f8af9
-- title:
--   SZ: tendsto design
-- statement:
--   The designed orbit tends to infinity.
--
--   Source: https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L63-L66
-- source:
--   https://github.com/rwst/Even-Integral/blob/b26ca4e4c4c36b4054e604456af86c2c924d742e/SZ/QuadraticDesign.lean#L63-L66

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_SZ_QuadraticDesign
set_option autoImplicit false
open SZ
open Real Filter
variable {α β : ℝ} {a b : ℤ}

theorem SZ.tendsto_design (h : Pair α β a b) (hβ : β < 0) :
    Tendsto (fun n : ℕ => xiDesign α β * α ^ n) atTop atTop := by sorry
