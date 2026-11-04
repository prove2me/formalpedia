-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankAssembly_product_abs
-- name    : ThreeSum.LightWeightedBankAssembly.product_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:21:54.904939+00:00
-- url     : https://prove2.me/theorems/f3285ca3-197b-4a74-a629-8dbb239961b9
-- title:
--   Light Weighted Bank Assembly: product abs
-- statement:
--   The Light Weighted Bank Assembly construction uses the product abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankAssembly.lean#L49-L55
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankAssembly.lean#L49-L55

import Definitions.Def_Submission_Weighted_BankStages
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_Submission_Weighted_BankAssembly
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}

theorem ThreeSum.LightWeightedBankAssembly.product_abs {N : ℕ} (F G : TritWord N→ℤ) (V : ℕ)
    (hF : ∀ R, |F R|≤(V : ℤ)) (hG : ∀ R, |G R|≤(V : ℤ)) (R : TritWord N) :
    |product F G R|≤(valueBound N V : ℤ) := by sorry
