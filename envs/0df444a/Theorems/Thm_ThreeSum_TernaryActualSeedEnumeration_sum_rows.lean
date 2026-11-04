-- Prove2me | Theorems.Thm_ThreeSum_TernaryActualSeedEnumeration_sum_rows
-- name    : ThreeSum.TernaryActualSeedEnumeration.sum_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:13:26.298738+00:00
-- url     : https://prove2.me/theorems/a37710dd-3e7f-4e05-92bd-314b7511a26f
-- title:
--   Ternary Actual Seed Enumeration: sum rows
-- statement:
--   Every seed counted in the average is visited once by the actual q²
--   integer loop, with no omitted or duplicated field pair.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L41-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryActualSeedEnumeration.lean#L41-L43

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

theorem ThreeSum.TernaryActualSeedEnumeration.sum_rows (hf : f.Monic) (score : Fin ((p^f.natDegree)*(p^f.natDegree))→ℕ) :
    (∑ i, score i)=∑ seed : AdjoinRoot f×AdjoinRoot f, score (equiv hf seed) := by sorry
