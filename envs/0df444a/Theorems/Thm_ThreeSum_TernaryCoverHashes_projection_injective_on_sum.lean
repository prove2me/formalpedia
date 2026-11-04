-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverHashes_projection_injective_on_sum
-- name    : ThreeSum.TernaryCoverHashes.projection_injective_on_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:22.315407+00:00
-- url     : https://prove2.me/theorems/37dbc1c3-f40b-4513-aa30-3b96e8886e35
-- title:
--   Ternary Cover Hashes: projection injective on sum
-- statement:
--   Unequal nonzero projection coefficients are injective inside every
--   fixed sum level.  This is the algebraic input to the projection majorization
--   argument; it is valid for all field characteristics.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L176-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverHashes.lean#L176-L184

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]

theorem ThreeSum.TernaryCoverHashes.projection_injective_on_sum {a b x y x' y' : K} (hab : a ≠ b)
    (hsum : x + y = x' + y')
    (hprojection : a * x + b * y = a * x' + b * y') :
    x = x' ∧ y = y' := by sorry
