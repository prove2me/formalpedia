-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandStep_tail_ends_w3sum_ac885d1
-- name    : ThreeSum.LightSourceBandStep.tail_ends_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:33:51.461342+00:00
-- url     : https://prove2.me/theorems/e7ed5533-a43e-401e-bc29-b1c9092ee97e
-- title:
--   Light Source Band Step: tail ends
-- statement:
--   The Light Source Band Step construction uses the tail ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandStep.lean#L55-L169
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandStep.lean#L55-L169

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_LightSourceBandStep
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandStep
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBandStep.tail_ends_w3sum_ac885d1 {pOriginal : ℕ} (C : LightSourceBucketOriginal.Procs P pOriginal)
    {μ : ℕ → ℤ} {src n g p m base U D i last : ℕ} {shift : ℤ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m) (hi : i < size n g)
    (hsrc : src+n ≤ base) (hlast : last=stop n g i)
    (hspace : LightSourceResidues.space (work base n g m) p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word n g p m U D : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (src+j)=f j) (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    Ends lim P d (tailBody pOriginal)
      ⟨frame [src,n,g,p,m,shift,base,cap n g,size n g,data base n g,stride n g m,
        work base n g m,i,start g i,last],μ⟩
      (tailTime n g p m U D) (fun σ =>
        SourceBandData.At σ.mem f base n g p m shift i ∧
        KeptBut μ σ.mem (hist base n g m i) (base+6*i) 6) := by sorry
