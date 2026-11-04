-- Prove2me | Theorems.Thm_ThreeSum_Cover_incidence_card_sum
-- name    : ThreeSum.Cover.incidence_card_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:04:53.724502+00:00
-- url     : https://prove2.me/theorems/cc320f74-7d74-4d86-83d4-4676d8302357
-- title:
--   Cover: incidence card sum
-- statement:
--   Exact double counting of the incidence relation.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Cover.lean#L87-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Cover.lean#L87-L93

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Cover
set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators

theorem ThreeSum.Cover.incidence_card_sum {Ω U : Type*} [Fintype Ω] [DecidableEq U]
    (targets : Finset U) (covers : Ω → U → Prop)
    [DecidableRel covers] :
    (∑ ω, (targets.filter (covers ω)).card) =
      ∑ u ∈ targets, (univ.filter fun ω => covers ω u).card := by sorry
