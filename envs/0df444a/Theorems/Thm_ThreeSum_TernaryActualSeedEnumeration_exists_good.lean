-- Prove2me | Theorems.Thm_ThreeSum_TernaryActualSeedEnumeration_exists_good
-- name    : ThreeSum.TernaryActualSeedEnumeration.exists_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:17.488106+00:00
-- url     : https://prove2.me/theorems/c6659a5a-07cf-425f-a737-c86efbb1b455
-- title:
--   Ternary Actual Seed Enumeration: exists good
-- statement:
--   The Ternary Actual Seed Enumeration construction uses the exists good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L45-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L45-L49

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

theorem ThreeSum.TernaryActualSeedEnumeration.exists_good (hf : f.Monic)
    (good : AdjoinRoot f×AdjoinRoot f→Prop) (h : ∃s, good s) :
    ∃i : Fin ((p^f.natDegree)*(p^f.natDegree)), good ((equiv hf).symm i) := by sorry
