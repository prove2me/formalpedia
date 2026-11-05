-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaQueryEncode_exists_query
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryEncode.exists_query
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:32:17.436703+00:00
-- url     : https://prove2.me/theorems/46ca3bd1-9913-4cd8-80cc-643a63e73323
-- title:
--   exists_query
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaQueryEncode.lean#L21-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaQueryEncode.lean#L21-L61

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryNative
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchInverse
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaQueryEncode
import Theorems.Thm_Light_Ends_block

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryEncode
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaQueryModel WeightedGlobalGoodOutputCatalog
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaQueryEncode.exists_query (maps : Fin F→Weight m p) (τ : ℕ) (targets : ℕ→ℤ)
    (positions : ℕ→ℕ) (n t : ℕ) (ht : t<n)
    (xs : Fin r→Record m (Fin F)) (hx : ∀ i, xs i∈records maps τ)
    (hdiv : (p : ℤ)^r∣targets t-Radix.positionalHash (p : ℤ) (key maps) (List.ofFn xs)) :
    ∃ j : Fin (queries (r := r) maps τ targets positions n).length,
      (descriptor maps τ targets positions n j).1=t ∧ block maps τ targets positions n j=xs := by sorry
