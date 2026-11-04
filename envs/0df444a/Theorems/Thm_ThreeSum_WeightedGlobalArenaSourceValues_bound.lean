-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceValues_bound
-- name    : ThreeSum.WeightedGlobalArenaSourceValues.bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:22:22.893074+00:00
-- url     : https://prove2.me/theorems/df1ed03e-ba0e-44bc-95fc-dd6cf8d23a60
-- title:
--   Weighted Global Arena Source Values: bound
-- statement:
--   The Weighted Global Arena Source Values construction uses the bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceValues.lean#L59-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceValues.lean#L59-L81

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceCertificate
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceValues
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaSourceValues
open Light TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps
open WeightedGlobalArenaSourceSetup WeightedGlobalNativeCompleteFrontend LightTernarySourceHost
open scoped BigOperators
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

theorem ThreeSum.WeightedGlobalArenaSourceValues.bound (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (weight : ℕ→ℤ) (g : ℕ) (W : TritWord (N m r))
    (hw : ∀i<(source (r := r) maps cap I right).NL, |weight i|≤(I.weightCap : ℤ)) :
    |(source (r := r) maps cap I right).values
      (WeightedBankCanonical.enumeration (N m r) (cut m r)).word weight g W|≤
      (valueCap (r := r) maps cap I : ℤ) := by sorry
