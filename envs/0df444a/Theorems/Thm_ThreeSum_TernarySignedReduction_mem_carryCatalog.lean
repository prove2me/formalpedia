-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedReduction_mem_carryCatalog
-- name    : ThreeSum.TernarySignedReduction.mem_carryCatalog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:37:38.991861+00:00
-- url     : https://prove2.me/theorems/42e9228a-3605-46af-9ee3-955bd74c146c
-- title:
--   Ternary Signed Reduction: mem carry Catalog
-- statement:
--   The Ternary Signed Reduction construction uses the mem carry Catalog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L53-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L53-L54

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset

theorem ThreeSum.TernarySignedReduction.mem_carryCatalog {J : ℕ} (c : CarryWord J) : c ∈ carryCatalog J ↔ ValidCarry c := by sorry
