-- Prove2me | Theorems.Thm_ThreeSum_LightSourceRowScan_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceRowScan.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:30:30.45495+00:00
-- url     : https://prove2.me/theorems/4fbff90f-87f0-43a1-b28e-b56241fba2cf
-- title:
--   Light Source Row Scan: meets
-- statement:
--   The Light Source Row Scan construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRowScan.lean#L83-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceRowScan.lean#L83-L180

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightSourceRowScan
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRowScan
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceRowScan.meets_w3sum_ac885d1 {pMain : ℕ} (hmain : P[pMain]? = some body)
    {μ : ℕ → ℤ} {src src0 src1 L dst U : ℕ} (bits w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+L ≤ lim.space) (hsrc0 : src0+L ≤ lim.space)
    (hsrc1 : src1+L ≤ lim.space) (hdst : dst+3 ≤ lim.space)
    (hword : (word L U : ℤ) ≤ lim.word)
    (hbits : ∀ i < L, μ (src+i) = (bits i : ℤ))
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbitBound : ∀ i < L, bits i ≤ 1)
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim P pMain d [src,src0,src1,L,dst] μ (time L) (fun _ ν =>
      ν dst = (count bits L : ℤ) ∧
      ν (dst+1) = (hash bits w0 w1 L : ℤ) ∧
      ν (dst+2) = (hash bits w1 w0 L : ℤ) ∧ SameOutside μ ν dst 3) := by sorry
