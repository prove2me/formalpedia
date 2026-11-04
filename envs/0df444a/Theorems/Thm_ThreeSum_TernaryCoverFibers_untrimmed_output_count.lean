-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverFibers_untrimmed_output_count
-- name    : ThreeSum.TernaryCoverFibers.untrimmed_output_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:26.170791+00:00
-- url     : https://prove2.me/theorems/4b312497-f9a4-4b09-aca9-936d334cab19
-- title:
--   Ternary Cover Fibers: untrimmed output count
-- statement:
--   Every output has its full, constant number of ordered partitions.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFibers.lean#L54-L90
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFibers.lean#L54-L90

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

theorem ThreeSum.TernaryCoverFibers.untrimmed_output_count (output : E → Q) (outputHash : Q → K)
    (left right : E → K) (G : ℕ)
    (hfiber : ∀ q : Q, (univ.filter fun e => output e = q).card = G)
    (hadd : ∀ e : E, left e + right e = outputHash (output e)) (o : K) :
    (univ.filter fun e => left e + right e = o).card =
      G * outputFiberCount outputHash o := by sorry
