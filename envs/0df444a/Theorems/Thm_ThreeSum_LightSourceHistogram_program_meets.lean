-- Prove2me | Theorems.Thm_ThreeSum_LightSourceHistogram_program_meets
-- name    : ThreeSum.LightSourceHistogram.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:46:24.337629+00:00
-- url     : https://prove2.me/theorems/0718ee50-d999-4335-b527-c7a8196fe959
-- title:
--   Light Source Histogram: program meets
-- statement:
--   The Light Source Histogram construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceHistogram.lean#L89-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceHistogram.lean#L89-L105

import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightSourceHistogram
import Theorems.Thm_ThreeSum_LightSourceResidues_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceHistogram
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceHistogram.program_meets
    {μ : ℕ → ℤ} {src hist n p m codes work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+n ≤ codes) (hhist : hist+m ≤ codes) (hcodes : codes+n ≤ work)
    (hspace : LightSourceResidues.space work p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    Meets lim program 0 d [src,hist,n,p,m,codes,work,shift] μ (time n p m U D)
      (fun _ ν =>
        (∀ i < n, ν (codes+i) =
          (LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
        (∀ r < m, ν (hist+r) = (LightHistogram.count
          (fun i => LightSourceResidues.key p m shift (μ (src+i))) r n : ℤ)) ∧
        KeptBut μ ν codes hist m) := by sorry
