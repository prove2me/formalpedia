-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverFibers_edge_count
-- name    : ThreeSum.TernaryCoverFibers.edge_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:49.381575+00:00
-- url     : https://prove2.me/theorems/c04d317a-5fc0-4088-b819-e04ac2aae151
-- title:
--   Ternary Cover Fibers: edge count
-- statement:
--   The total number of edges is outputs times partitions per output.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFibers.lean#L107-L114
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFibers.lean#L107-L114

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

theorem ThreeSum.TernaryCoverFibers.edge_count (output : E → Q) (G : ℕ)
    (hfiber : ∀ q : Q, (univ.filter fun e => output e = q).card = G) :
    Fintype.card E = Fintype.card Q * G := by sorry
