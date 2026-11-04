-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBandSetup_address_ends
-- name    : ThreeSum.LightSourceBandSetup.address_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:34:01.444896+00:00
-- url     : https://prove2.me/theorems/2c6eb370-cb83-4bab-bd6e-3848f62457bf
-- title:
--   Light Source Band Setup: address ends
-- statement:
--   The Light Source Band Setup construction uses the address ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandSetup.lean#L53-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBandSetup.lean#L53-L99

import Definitions.Def_Submission_ThreeSum_LightSourceBandBatch
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBandSetup
open Light BandPartition SourceBandLayout
set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBandSetup.address_ends {pBatch : ℕ} (C : LightSourceBandBatch.Procs P pBatch)
    {μ : ℕ → ℤ} {src n g p m base U D K : ℕ} {shift : ℤ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+5 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ base) (hK : K=size n g)
    (hspace : LightSourceResidues.space (work base n g m) p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (LightSourceBandStep.word n g p m U D : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (src+j)=f j) (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    Ends lim P d (addressBody pBatch)
      ⟨frame [src,n,g,p,m,shift,base,cap n g,K],μ⟩
      (addressTime n g p m U D) (fun σ =>
        σ.loc 0=(work base n g m : ℤ) ∧
        (∀ i < size n g, SourceBandData.At σ.mem f base n g p m shift i) ∧ Kept μ σ.mem base) := by sorry
