-- Prove2me | Theorems.Thm_ThreeSum_LightSourceBucketOriginal_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightSourceBucketOriginal.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:51:01.535636+00:00
-- url     : https://prove2.me/theorems/422bb73e-e9f1-4d1b-a0cd-5e6011eefcec
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketOriginal.lean#L35-L79
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceBucketOriginal.lean#L35-L79

import Definitions.Def_Submission_ThreeSum_LightSourceBucketFromHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_WeightedCache3SUM_Alias_8c6e823b5fcef3e6
import Definitions.Def_WeightedCache3SUM_Alias_3b570d79c28763f9
import Definitions.Def_WeightedCache3SUM_Alias_075817043fa4e845
import Definitions.Def_WeightedCache3SUM_Alias_5b14bc7229a63f1e
import Theorems.Thm_ThreeSum_LightSourceResidues_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceBucketOriginal
open Light SourceBuckets LightHistogram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceBucketOriginal.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {src N p m hist codes offsets cursor flat work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+N ≤ hist) (hhist : hist+m ≤ codes) (hcodes : codes+N ≤ offsets)
    (hoffsets : offsets+m+1 ≤ cursor) (hcursor : cursor+m ≤ flat) (hflat : flat+N ≤ work)
    (hspace : LightSourceResidues.space work p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [(src : ℤ),(N : ℤ),(p : ℤ),(m : ℤ),shift,(hist : ℤ),(codes : ℤ),
        (offsets : ℤ),(cursor : ℤ),(flat : ℤ),(work : ℤ)]
      μ (time N p m U D) (fun _ ν =>
        Stored ν (fun i => LightSourceResidues.key p m shift (μ (src+i))) N m offsets flat ∧
        (∀ r < m, ν (hist+r) = (count
          (fun i => LightSourceResidues.key p m shift (μ (src+i))) r N : ℤ)) ∧
        (∀ i < N, ν (codes+i) = (LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
        Kept μ ν hist) := by sorry
