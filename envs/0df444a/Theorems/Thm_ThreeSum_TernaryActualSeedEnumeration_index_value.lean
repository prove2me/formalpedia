-- Prove2me | Theorems.Thm_ThreeSum_TernaryActualSeedEnumeration_index_value
-- name    : ThreeSum.TernaryActualSeedEnumeration.index_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:37:43.837196+00:00
-- url     : https://prove2.me/theorems/b76ff1a9-cfbb-4fe6-b0b5-a723ed970697
-- title:
--   Ternary Actual Seed Enumeration: index value
-- statement:
--   The Ternary Actual Seed Enumeration construction uses the index value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L15-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L15-L16

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

theorem ThreeSum.TernaryActualSeedEnumeration.index_value (hf : f.Monic) (x y : AdjoinRoot f) :
    (equiv hf (x,y)).val=encode hf y+p^f.natDegree*encode hf x := by sorry
