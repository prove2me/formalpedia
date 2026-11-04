-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankAssembly_product_abs
-- name    : ThreeSum.LightTernaryBankAssembly.product_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:30:05.199939+00:00
-- url     : https://prove2.me/theorems/d7e1b312-54a9-477f-9aa0-b83831445759
-- title:
--   Light Ternary Bank Assembly: product abs
-- statement:
--   The Light Ternary Bank Assembly construction uses the product abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankAssembly.lean#L44-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankAssembly.lean#L44-L50

import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}

theorem ThreeSum.LightTernaryBankAssembly.product_abs {N : ℕ} (F G : TritWord N→ℤ) (V : ℕ)
    (hF : ∀ R, |F R|≤(V : ℤ)) (hG : ∀ R, |G R|≤(V : ℤ)) (R : TritWord N) :
    |product F G R|≤(valueBound N V : ℤ) := by sorry
