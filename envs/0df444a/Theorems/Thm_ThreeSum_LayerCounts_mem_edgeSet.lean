-- Prove2me | Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
-- name    : ThreeSum.LayerCounts.mem_edgeSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:04:42.63939+00:00
-- url     : https://prove2.me/theorems/3bee9df0-fa75-4511-9d68-b0d69ccefae1
-- title:
--   Layer Counts: mem edge Set
-- statement:
--   The Layer Counts construction uses the mem edge Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LayerCounts.lean#L33-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LayerCounts.lean#L33-L35

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

theorem ThreeSum.LayerCounts.mem_edgeSet {L h : ℕ} {p : Finset (Fin L) × Finset (Fin L)} :
    p ∈ edgeSet L h ↔ p.1.card = h ∧ p.2.card = h ∧ Disjoint p.1 p.2 := by sorry
