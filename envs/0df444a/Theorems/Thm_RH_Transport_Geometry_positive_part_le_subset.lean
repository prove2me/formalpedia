-- Prove2me | Theorems.Thm_RH_Transport_Geometry_positive_part_le_subset
-- name    : RH.Transport.Geometry.positive_part_le_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:43:39.149973+00:00
-- url     : https://prove2.me/theorems/cd51c135-d993-470f-86ac-f1ea94663795
-- title:
--   Geometry: positive part le subset
-- statement:
--   The positive-part term is bounded by the subset length. This uses only
--   the upper bound on p and nonnegativity of d; an upper bound on d
--   is unnecessary for this particular inequality.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L189-L195
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean#L189-L195

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Transport_Geometry
set_option autoImplicit false
open RH RH.Transport RH.Transport.Geometry
noncomputable section

theorem RH.Transport.Geometry.positive_part_le_subset {p d : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) :
    max 0 (5 * ell p - 1 + d) ≤ d := by sorry
