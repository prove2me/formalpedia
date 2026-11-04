-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedSourceCountHost_program_meets
-- name    : ThreeSum.LightWeightedSourceCountHost.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:22:35.161959+00:00
-- url     : https://prove2.me/theorems/6b5e12ae-9176-43b0-859d-51c28cfca1a0
-- title:
--   Light Weighted Source Count Host: program meets
-- statement:
--   Composition uses execution receipts of the actual included source and
--   counting libraries. In particular, neither input histogram is advice: both
--   are established by preceding calls. The source receipts are discharged by
--   `LightTernarySourceHost.program_meets` and the counting receipt by
--   `LightWeightedCountFrontend.meets`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L139-L206
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/SourceCountHost.lean#L139-L206

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_Weighted_SourceCountHost
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCacheEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightMaskBits_program_meets
import Theorems.Thm_ThreeSum_LightMaskErase_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
import Theorems.Thm_ThreeSum_LightOutputDecodeDivide_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_program_meets
import Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_program_meets
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_program_meets
import Theorems.Thm_ThreeSum_LightTernarySourceHost_program_meets
import Theorems.Thm_ThreeSum_LightWantedJoin_program_meets
import Definitions.Def_WeightedCache3SUM_Alias_631140e497667d8d
import Theorems.Thm_ThreeSum_LightWeightedCost_program_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_program_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedSourceCountHost.program_meets {lim : Limits} {d TL TR TC keepLeft keepRight keepFront
    fbase gbase groups bank count dst : ℕ}
    (xl yl zl xr yr zr left right frontend : List ℤ) (μ : ℕ → ℤ)
    (F G : ℕ → ℕ → ℤ) (value : ℕ → ℤ)
    (hl : left.length=23) (hr : right.length=23) (hf : frontend.length=60)
    (hkeepRight : keepLeft≤keepRight) (hkeepFront : keepLeft≤keepFront)
    (hFend : fbase+groups*bank≤keepRight)
    (hleft : Meets lim (LightTernarySourceHost.program xl yl zl) 34 (d+1) left μ TL
      (fun _ ν => Kept μ ν keepLeft ∧ BankReads ν fbase groups bank F))
    (hright : ∀ ν, Kept μ ν keepLeft →
      Meets lim (LightTernarySourceHost.program xr yr zr) 34 (d+1) right ν TR
        (fun _ ξ => Kept ν ξ keepRight ∧ BankReads ξ gbase groups bank G))
    (hfrontend : ∀ ν, Kept μ ν keepLeft →
      BankReads ν fbase groups bank F → BankReads ν gbase groups bank G →
      Meets lim LightWeightedCountFrontend.program 63 (d+1) frontend ν TC
        (fun _ ξ => Kept ν ξ keepFront ∧ ∀ j<count, ξ (dst+j)=value j))
    (hd : d<lim.depth) :
    Meets lim (program xl yl zl xr yr zr) 134 d (args left right frontend) μ
      (time TL TR TC)
      (fun _ ν => Kept μ ν keepLeft ∧ ∀ j<count, ν (dst+j)=value j) := by sorry
