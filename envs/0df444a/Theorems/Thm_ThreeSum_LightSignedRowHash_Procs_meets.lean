-- Prove2me | Theorems.Thm_ThreeSum_LightSignedRowHash_Procs_meets
-- name    : ThreeSum.LightSignedRowHash.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:27.984681+00:00
-- url     : https://prove2.me/theorems/55f9c19e-f0cd-4476-b51f-28d7caa20a2e
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedRowHash.lean#L35-L81
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSignedRowHash.lean#L35-L81

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightNaturalDot
import Definitions.Def_Submission_ThreeSum_LightSignedRowHash
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedRowHash
open Light
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightSignedRowHash.Procs.meets {main src row dst n p b : ℕ} (S : Procs P main)
    (μ : ℕ → ℤ) (z : ℕ → ℤ) (coeff : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+2<lim.depth) (hbp : b<p)
    (hsrc : src+n≤dst) (hrow : row+n≤dst) (hspace : dst+n≤lim.space)
    (hzRead : ∀ i<n, μ (src+i)=z i) (hcRead : ∀ i<n, μ (row+i)=(coeff i : ℤ))
    (hzBound : ∀ i<n, |z i|≤(b : ℤ)) (hcBound : ∀ i<n, coeff i≤p)
    (hword : (word n p b : ℤ)≤lim.word) :
    Meets lim P main depth [src,row,dst,n,p] μ (time n p b)
      (fun r ν => r=(((LightNaturalDot.dot coeff (fun i => lifted p (z i)) n)%p : ℕ) : ℤ) ∧
        SameOutside μ ν dst n) := by sorry
