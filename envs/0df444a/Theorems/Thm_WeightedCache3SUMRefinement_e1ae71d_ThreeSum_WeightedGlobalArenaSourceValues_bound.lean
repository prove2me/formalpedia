-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalArenaSourceValues_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceValues.bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T13:13:29.647405+00:00
-- url     : https://prove2.me/theorems/dbb2ddcc-8084-4126-b53a-869b4eb00e5f
-- title:
--   bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceValues.lean#L59-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryArenaSourceValues.lean#L59-L81

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSourceValues
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceValues
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend LightTernarySourceHost
open scoped BigOperators
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalArenaSourceValues.bound (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (weight : ℕ→ℤ) (g : ℕ) (W : TritWord (N m r))
    (hw : ∀i<(source (r := r) maps cap I right).NL, |weight i|≤(I.weightCap : ℤ)) :
    |(source (r := r) maps cap I right).values
      (WeightedBankCanonical.enumeration (N m r) (cut m r)).word weight g W|≤
      (valueCap (r := r) maps cap I : ℤ) := by sorry
