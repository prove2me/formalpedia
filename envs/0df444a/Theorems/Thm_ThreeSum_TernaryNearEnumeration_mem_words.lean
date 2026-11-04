-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_words
-- name    : ThreeSum.TernaryNearEnumeration.mem_words
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:18.317196+00:00
-- url     : https://prove2.me/theorems/e807751f-3f9e-42fb-ba02-abb01d3d720d
-- title:
--   Ternary Near Enumeration: mem words
-- statement:
--   The Ternary Near Enumeration construction uses the mem words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L36-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L36-L49

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_words

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.mem_words (qs rs : List ℕ) (D : ℕ) : rs ∈ words qs D ↔ Admitted qs rs D := by sorry
