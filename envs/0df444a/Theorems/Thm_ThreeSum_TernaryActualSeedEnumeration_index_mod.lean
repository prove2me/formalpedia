-- Prove2me | Theorems.Thm_ThreeSum_TernaryActualSeedEnumeration_index_mod
-- name    : ThreeSum.TernaryActualSeedEnumeration.index_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:31.208201+00:00
-- url     : https://prove2.me/theorems/7c306f07-9b19-48cd-aa28-43650c6cc25c
-- title:
--   Ternary Actual Seed Enumeration: index mod
-- statement:
--   The Ternary Actual Seed Enumeration construction uses the index mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L23-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L23-L25

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

theorem ThreeSum.TernaryActualSeedEnumeration.index_mod (hf : f.Monic) (x y : AdjoinRoot f) :
    (equiv hf (x,y)).val%(p^f.natDegree)=encode hf y := by sorry
