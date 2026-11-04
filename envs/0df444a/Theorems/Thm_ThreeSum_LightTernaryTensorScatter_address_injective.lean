-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryTensorScatter_address_injective
-- name    : ThreeSum.LightTernaryTensorScatter.address_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:13.709533+00:00
-- url     : https://prove2.me/theorems/82411561-96c5-4b58-a3aa-4638a8a43df1
-- title:
--   Light Ternary Tensor Scatter: address injective
-- statement:
--   The Light Ternary Tensor Scatter construction uses the address injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryTensorScatter.lean#L7-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryTensorScatter.lean#L7-L19

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryTensorScatter
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryTensorScatter
open Light
set_option maxHeartbeats 1800000

theorem ThreeSum.LightTernaryTensorScatter.address_injective {W a b q r : ℕ} (hq : q<W) (hr : r<W)
    (h : a*W+q=b*W+r) : a=b ∧ q=r := by sorry
