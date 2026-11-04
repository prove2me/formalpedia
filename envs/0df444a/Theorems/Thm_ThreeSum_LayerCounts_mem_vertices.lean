-- Prove2me | Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
-- name    : ThreeSum.LayerCounts.mem_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:03:11.48178+00:00
-- url     : https://prove2.me/theorems/5653df0f-4c46-4171-9f83-0bc729593cf6
-- title:
--   Layer Counts: mem vertices
-- statement:
--   The Layer Counts construction uses the mem vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LayerCounts.lean#L26-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LayerCounts.lean#L26-L28

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_LayerCounts
set_option autoImplicit false
open ThreeSum ThreeSum.LayerCounts
open Finset

theorem ThreeSum.LayerCounts.mem_vertices {L h : ℕ} {S : Finset (Fin L)} :
    S ∈ vertices L h ↔ S.card = h := by sorry
