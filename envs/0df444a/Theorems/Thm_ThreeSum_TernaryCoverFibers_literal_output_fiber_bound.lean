-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverFibers_literal_output_fiber_bound
-- name    : ThreeSum.TernaryCoverFibers.literal_output_fiber_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:45.554305+00:00
-- url     : https://prove2.me/theorems/4fac592f-36a6-4c80-a9dd-52e31e8e0954
-- title:
--   Ternary Cover Fibers: literal output fiber bound
-- statement:
--   The literal output bound uses raw ordered fibers, not the retained
--   endpoint-bucket bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFibers.lean#L94-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFibers.lean#L94-L104

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverFibers
open Finset
open scoped BigOperators
variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
variable [DecidableEq Q] [DecidableEq K] [AddCommGroup K]

theorem ThreeSum.TernaryCoverFibers.literal_output_fiber_bound (output : E → Q) (outputHash : Q → K)
    (left right : E → K) (G τ : ℕ)
    (hfiber : ∀ q : Q, (univ.filter fun e => output e = q).card = G)
    (hadd : ∀ e : E, left e + right e = outputHash (output e))
    (hraw : ∀ a b : K, rawPairCount left right a b ≤ τ) (o : K) :
    G * outputFiberCount outputHash o ≤ Fintype.card K * τ := by sorry
