-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryAppendKeys_Procs_meets
-- name    : ThreeSum.LightTernaryAppendKeys.Procs.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:41:47.094243+00:00
-- url     : https://prove2.me/theorems/b6ba72dd-838b-4573-94a2-1a80371b44aa
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryAppendKeys.lean#L32-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryAppendKeys.lean#L32-L118

import Definitions.Def_Submission_ThreeSum_LightSignedRowHash
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Theorems.Thm_ThreeSum_LightNaturalDot_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Theorems.Thm_ThreeSum_LightSignedRowHash_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryAppendKeys
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightTernaryAppendKeys.Procs.meets {main matrix row oldBase dst n len p power scratch b : ℕ}
    (S : Procs P main) (μ : ℕ → ℤ) (old : ℕ → ℕ) (z : ℕ → ℕ → ℤ) (c : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+3<lim.depth) (hbp : b<p)
    (hmatrix : matrix+n*len≤dst) (hrow : row+len≤dst) (hold : oldBase+n≤dst)
    (hout : dst+n≤scratch) (hspace : scratch+len≤lim.space)
    (hmRead : ∀ i<n, ∀ k<len, μ (matrix+i*len+k)=z i k)
    (hcRead : ∀ k<len, μ (row+k)=(c k : ℤ))
    (hoRead : ∀ i<n, μ (oldBase+i)=(old i : ℤ))
    (hzBound : ∀ i<n, ∀ k<len, |z i k|≤(b : ℤ))
    (hcBound : ∀ k<len, c k≤p) (hoBound : ∀ i<n, old i<power)
    (hword : (word len p b power : ℤ)≤lim.word) :
    Meets lim P main depth [matrix,row,oldBase,dst,n,len,p,power,scratch] μ (time n len p b)
      (fun _ ν => (∀ i<n, ν (dst+i)=(key p power len old z c i : ℤ)) ∧ Kept μ ν dst) := by sorry
