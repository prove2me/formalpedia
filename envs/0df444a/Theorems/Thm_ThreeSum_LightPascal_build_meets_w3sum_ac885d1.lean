-- Prove2me | Theorems.Thm_ThreeSum_LightPascal_build_meets_w3sum_ac885d1
-- name    : ThreeSum.LightPascal.build_meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:20.849848+00:00
-- url     : https://prove2.me/theorems/aa2ee822-6139-49a0-a10c-cb29f5386e79
-- title:
--   Light Pascal: build meets
-- statement:
--   The Light Pascal construction uses the build meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPascal.lean#L92-L165
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPascal.lean#L92-L165

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_ThreeSum_LightPascal
set_option autoImplicit false
open ThreeSum ThreeSum.LightPascal
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightPascal.build_meets_w3sum_ac885d1 {pBuild pFill pRow pLinear : ℕ}
    (hbuild : P[pBuild]? = some (buildBody pFill pRow))
    (hfill : P[pFill]? = some fillBody)
    (hrow : P[pRow]? = some (rowBody pLinear))
    (hlinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {dst L : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hspace : dst+tableSize L ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pBuild d [dst,L] μ (buildTime L) fun _ μ' =>
      Table μ' dst L ∧ SameOutside μ μ' dst (tableSize L) := by sorry
