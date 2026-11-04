-- Prove2me | Theorems.Thm_ThreeSum_TernaryActualSeedEnumeration_index_div
-- name    : ThreeSum.TernaryActualSeedEnumeration.index_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:28.057001+00:00
-- url     : https://prove2.me/theorems/48d0bf46-4592-4d64-bfa7-f279290ad958
-- title:
--   Ternary Actual Seed Enumeration: index div
-- statement:
--   The Ternary Actual Seed Enumeration construction uses the index div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L18-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L18-L21

import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_ThreeSum_LightExtensionSeedMatrix
import Definitions.Def_Submission_ThreeSum_TernaryActualSeedEnumeration
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryActualSeedEnumeration
open TernaryExtensionEncoding Polynomial
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryActualSeedEnumeration.index_div (hf : f.Monic) (x y : AdjoinRoot f) :
    (equiv hf (x,y)).val/(p^f.natDegree)=encode hf x := by sorry
