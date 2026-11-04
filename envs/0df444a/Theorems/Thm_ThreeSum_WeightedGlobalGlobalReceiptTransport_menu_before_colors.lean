-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalGlobalReceiptTransport_menu_before_colors
-- name    : ThreeSum.WeightedGlobalGlobalReceiptTransport.menu_before_colors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T22:00:54.831953+00:00
-- url     : https://prove2.me/theorems/6b2d820c-1963-4cf2-a10b-249d4c6c116a
-- title:
--   Weighted Global Global Receipt Transport: menu before colors
-- statement:
--   The Weighted Global Global Receipt Transport construction uses the menu before colors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalReceiptTransport.lean#L48-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryGlobalReceiptTransport.lean#L48-L54

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
import Definitions.Def_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalReceiptTransport
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalGlobalReceiptTransport
open Light LightWeightedGlobalGlobalPrelude LightWeightedGlobalFastProgramProof LightExtensionBackendLayout
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedGlobalGlobalReceiptTransport.menu_before_colors (M b p K κ n free : ℕ) :
    physical (backend free) (LightWeightedGlobalDimensions.dim M b p K n (n^κ))
      (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ))) (LightWeightedGlobalDimensions.J M b n (n^κ))+
      (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ)))*
        (p^(LightWeightedGlobalDimensions.dim M b p K n (n^κ)))*
        (LightWeightedGlobalDimensions.J M b n (n^κ)+2)≤scanFree M b p K κ n free := by sorry
