-- Prove2me | Theorems.Thm_ThreeSum_LightWeightDecode_Rows_decodedWeight
-- name    : ThreeSum.LightWeightDecode.Rows.decodedWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:35.511078+00:00
-- url     : https://prove2.me/theorems/f2d9217a-91e3-4a17-a2b3-43c8622042e3
-- title:
--   Rows: decoded Weight
-- statement:
--   The Rows construction uses the decoded Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightDecode.lean#L126-L131
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightWeightDecode.lean#L126-L131

import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightWeightDecode
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightDecode
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightWeightDecode.Rows.decodedWeight {μ : ℕ → ℤ} {dst L p k : ℕ}
    (hrows : Rows μ dst L p k) (i : Fin L) :
    μ (dst+i.val) = ((WeightEnumeration.decodedWeight (K := ZMod p) L p k (i,false)).val : ℤ) ∧
    μ (dst+L+i.val) = ((WeightEnumeration.decodedWeight (K := ZMod p) L p k (i,true)).val : ℤ) := by sorry
