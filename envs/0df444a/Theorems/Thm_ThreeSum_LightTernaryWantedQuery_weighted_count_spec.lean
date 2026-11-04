-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedQuery_weighted_count_spec
-- name    : ThreeSum.LightTernaryWantedQuery.weighted_count_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:21:44.226085+00:00
-- url     : https://prove2.me/theorems/cf9e9d87-dc6c-463c-89ec-cfe18691d1ea
-- title:
--   Light Ternary Wanted Query: weighted count spec
-- statement:
--   Rewrite the actual physical result to the original additive count. This
--   uses the proved full-stage factorial convolution identity.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedQuery.lean#L159-L172
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedQuery.lean#L159-L172

import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPhysical
import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedQuery
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryWantedQuery.weighted_count_spec {N a b pMain d t : ℕ} (argv : List ℤ) (μ : ℕ→ℤ)
    (f g : TritWord N→ℤ) (Q : TritWord N) (keep : ℕ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (hQ : rank Q=a+b)
    (hquery : Meets lim P pMain d argv μ t (fun v ν =>
      v=stageValue N (H (fun A => ThreeSum.TernaryConvolution.factorial A*f A)
        (fun B => ThreeSum.TernaryConvolution.factorial B*g B)) Q ∧ Kept μ ν keep)) :
    Meets lim P pMain d argv μ t (fun v ν =>
      v=ThreeSum.TernaryConvolution.factorial Q*ThreeSum.TernaryConvolution.convolution f g Q ∧
        Kept μ ν keep) := by sorry
