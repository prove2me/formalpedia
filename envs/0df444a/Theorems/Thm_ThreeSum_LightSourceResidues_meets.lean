-- Prove2me | Theorems.Thm_ThreeSum_LightSourceResidues_meets
-- name    : ThreeSum.LightSourceResidues.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:27:23.404725+00:00
-- url     : https://prove2.me/theorems/045c10f5-7b51-4eb6-8e57-2ed9c3ab215f
-- title:
--   Light Source Residues: meets
-- statement:
--   The Light Source Residues construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceResidues.lean#L134-L145
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceResidues.lean#L134-L145

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceResidues.meets {pMain pEmod : ℕ}
    (hmain : P[pMain]? = some (body pEmod)) (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {src dst n p m work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ work) (hdst : dst+n ≤ work)
    (hspace : space work p U D ≤ lim.space) (hsep : Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,dst,n,p,m,work,shift] μ (time n p U D) (fun _ ν =>
      (∀ i < n, ν (dst+i) = (key p m shift (μ (src+i)) : ℤ)) ∧
      KeptBut μ ν work dst n) := by sorry
