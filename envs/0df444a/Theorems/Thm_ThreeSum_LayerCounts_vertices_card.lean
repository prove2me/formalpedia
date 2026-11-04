-- Prove2me | Theorems.Thm_ThreeSum_LayerCounts_vertices_card
-- name    : ThreeSum.LayerCounts.vertices_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:03:12.709131+00:00
-- url     : https://prove2.me/theorems/d9b62fdb-1577-4dee-9130-710015ccfb0a
-- title:
--   Layer Counts: vertices card
-- statement:
--   The Layer Counts construction uses the vertices card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LayerCounts.lean#L30-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LayerCounts.lean#L30-L31

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

theorem ThreeSum.LayerCounts.vertices_card (L h : ℕ) : (vertices L h).card = L.choose h := by sorry
