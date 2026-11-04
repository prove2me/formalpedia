-- Prove2me | Theorems.Thm_ThreeSum_LightPascal_row_meets
-- name    : ThreeSum.LightPascal.row_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:25:43.206983+00:00
-- url     : https://prove2.me/theorems/6cc2136e-0708-447c-beef-366b49313f14
-- title:
--   Light Pascal: row meets
-- statement:
--   The Light Pascal construction uses the row meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPascal.lean#L29-L75
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPascal.lean#L29-L75

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_ThreeSum_LightPascal
set_option autoImplicit false
open ThreeSum ThreeSum.LightPascal
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightPascal.row_meets {pRow pLinear : ℕ}
    (hrow : P[pRow]? = some (rowBody pLinear))
    (hlinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst L i : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+(L+1) ≤ lim.space) (hdst : dst+(L+1) ≤ lim.space)
    (hsep : Apart src (L+1) dst (L+1)) (hi : i ≤ L)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalues : ∀ j ≤ L, μ (src+j) = (i.choose j : ℤ)) :
    Meets lim P pRow d [src,dst,L] μ (rowTime L) fun _ μ' =>
      (∀ j ≤ L, μ' (dst+j) = ((i+1).choose j : ℤ)) ∧
        SameOutside μ μ' dst (L+1) := by sorry
