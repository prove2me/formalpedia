-- Prove2me | Theorems.Thm_ThreeSum_LightResidues_residues_ends_w3sum_ac885d1
-- name    : ThreeSum.LightResidues.residues_ends_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:10:07.590242+00:00
-- url     : https://prove2.me/theorems/05a1c0d4-30f1-4ea1-8485-de31e8341746
-- title:
--   Light Residues: residues ends
-- statement:
--   Every call uses the same scratch region; only the destination can change
--   below it. The source and destination are disjoint.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidues.lean#L56-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidues.lean#L56-L115

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightResidues
set_option autoImplicit false
open ThreeSum ThreeSum.LightResidues
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightResidues.residues_ends_w3sum_ac885d1 {pEmod : ℕ}
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {src dst n p work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hsrc : src + n ≤ work) (hdst : dst + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hsep : Apart src n dst n) (hc : |c| ≤ 1)
    (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Ends lim P d (residuesBody pEmod) ⟨frame [src, dst, n, p, work, c], μ⟩
      (residuesTime n U) fun σ' =>
        (∀ i < n, σ'.mem (dst + i) = (residue p c (μ (src + i)) : ℤ)) ∧
          KeptBut μ σ'.mem work dst n := by sorry
