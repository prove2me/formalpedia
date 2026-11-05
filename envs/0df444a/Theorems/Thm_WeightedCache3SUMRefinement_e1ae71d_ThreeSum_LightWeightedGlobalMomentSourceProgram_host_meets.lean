-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedGlobalMomentSourceProgram_host_meets
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram.host_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:10:14.748195+00:00
-- url     : https://prove2.me/theorems/d387102f-9f89-4ac7-8708-0ef586584d31
-- title:
--   host_meets
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentSourceProgram.lean#L81-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/LightTernaryMomentSourceProgram.lean#L81-L104

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountHost
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannelStep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryMomentSourceProgram
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram
open Light TernaryWeightChannels

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedGlobalMomentSourceProgram.host_meets {lim : Limits} {d TL TR TC keepLeft keepRight keepFront
    fbase gbase groups bank count dst k j : ℕ}
    (xl yl zl xr yr zr left right frontend : List ℤ) (μ : ℕ→ℤ)
    (F G : ℕ→ℕ→ℤ) (value : ℕ→ℤ)
    (hl : left.length=23) (hr : right.length=23) (hf : frontend.length=60)
    (hkeepRight : keepLeft≤keepRight) (hkeepFront : keepLeft≤keepFront)
    (hFend : fbase+groups*bank≤keepRight)
    (hleft : Meets lim (LightTernarySourceHost.program xl yl zl) 34 (d+1) left μ TL
      (fun _ ν => Kept μ ν keepLeft ∧ LightWeightedSourceCountHost.BankReads ν fbase groups bank F))
    (hright : ∀ ν, Kept μ ν keepLeft →
      Meets lim (LightTernarySourceHost.program xr yr zr) 34 (d+1) right ν TR
        (fun _ ξ => Kept ν ξ keepRight ∧ LightWeightedSourceCountHost.BankReads ξ gbase groups bank G))
    (hfrontend : ∀ ν, Kept μ ν keepLeft →
      LightWeightedSourceCountHost.BankReads ν fbase groups bank F →
      LightWeightedSourceCountHost.BankReads ν gbase groups bank G →
      Meets lim LightWeightedCountFrontend.program 63 (d+1) frontend ν TC
        (fun _ ξ => Kept ν ξ keepFront ∧ ∀ i<count, ξ (dst+i)=value i))
    (hd : d<lim.depth) :
    Meets lim (program xl yl zl xr yr zr k j) 134 d
      (LightWeightedSourceCountHost.args left right frontend) μ
      (LightWeightedSourceCountHost.time TL TR TC)
      (fun _ ν => Kept μ ν keepLeft ∧ ∀ i<count, ν (dst+i)=value i) := by sorry
