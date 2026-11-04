-- Prove2me | Theorems.Thm_ThreeSum_LightSourceResidues_ends_w3sum_ac885d1
-- name    : ThreeSum.LightSourceResidues.ends_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:18:39.917739+00:00
-- url     : https://prove2.me/theorems/bca9fc2b-f49a-4b90-bfb6-2b2328a7441e
-- title:
--   Light Source Residues: ends
-- statement:
--   The Light Source Residues construction uses the ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceResidues.lean#L55-L132
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceResidues.lean#L55-L132

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceResidues.ends_w3sum_ac885d1 {pEmod : ℕ} (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {src dst n p m work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+n ≤ work) (hdst : dst+n ≤ work)
    (hspace : space work p U D ≤ lim.space) (hsep : Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    Ends lim P d (body pEmod) ⟨frame [src,dst,n,p,m,work,shift],μ⟩
      (time n p U D) (fun σ =>
        (∀ i < n, σ.mem (dst+i) = (key p m shift (μ (src+i)) : ℤ)) ∧
        KeptBut μ σ.mem work dst n) := by sorry
