-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyEnumeration_rawOutput_abs_le_w3sum_ac885d1
-- name    : ThreeSum.GlobalKeyEnumeration.rawOutput_abs_le_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:48.282047+00:00
-- url     : https://prove2.me/theorems/d11045e7-0039-4ea0-a729-271f16b66c19
-- title:
--   Global Key Enumeration: raw Output abs le
-- statement:
--   The Global Key Enumeration construction uses the raw Output abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L124-L141
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L124-L141

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem ThreeSum.GlobalKeyEnumeration.rawOutput_abs_le_w3sum_ac885d1 {h L : ℕ} (w : Weight L (LocalField h))
    (Q : Finset (Fin L)) : |rawOutput w Q| ≤ ((L*localPrime h : ℕ) : ℤ) := by sorry
