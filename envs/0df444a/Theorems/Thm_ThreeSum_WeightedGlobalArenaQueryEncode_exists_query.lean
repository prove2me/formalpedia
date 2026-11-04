-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryEncode_exists_query
-- name    : ThreeSum.WeightedGlobalArenaQueryEncode.exists_query
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:45:59.73461+00:00
-- url     : https://prove2.me/theorems/2e248cd5-6b53-495c-8015-7b7c5f5acf6e
-- title:
--   Weighted Global Arena Query Encode: exists query
-- statement:
--   Every retained output tuple with a literal original target has one
--   actual DFS output ordinal, retaining its target/carry occurrence.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryEncode.lean#L21-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaQueryEncode.lean#L21-L61

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchInverse
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryEncode
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryEncode
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaQueryModel WeightedGlobalGoodOutputCatalog
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaQueryEncode.exists_query (maps : Fin F→Weight m p) (τ : ℕ) (targets : ℕ→ℤ)
    (positions : ℕ→ℕ) (n t : ℕ) (ht : t<n)
    (xs : Fin r→Record m (Fin F)) (hx : ∀ i, xs i∈records maps τ)
    (hdiv : (p : ℤ)^r∣targets t-Radix.positionalHash (p : ℤ) (key maps) (List.ofFn xs)) :
    ∃ j : Fin (queries (r := r) maps τ targets positions n).length,
      (descriptor maps τ targets positions n j).1=t ∧ block maps τ targets positions n j=xs := by sorry
