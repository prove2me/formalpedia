-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryProduct_meets
-- name    : ThreeSum.LightTernaryProduct.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:49.177849+00:00
-- url     : https://prove2.me/theorems/5a251bd0-97a9-491e-9151-79f9d2c3aabe
-- title:
--   Light Ternary Product: meets
-- statement:
--   The Light Ternary Product construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryProduct.lean#L16-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryProduct.lean#L16-L37

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryProduct
open Light ThreeSum.LightArray
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryProduct.meets {p a b dst n U V : ℕ} (hprog : P[p]? = some body)
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hb : b+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsepA : SourceSafe a dst n) (hsepB : SourceSafe b dst n)
    (hA : ∀ j < n, |μ (a+j)| ≤ U) (hB : ∀ j < n, |μ (b+j)| ≤ V)
    (hword : (U : ℤ)*(V : ℤ) ≤ lim.word) :
    Meets lim P p d [a,b,dst,n] μ (time n)
      (fun _ μ' => (∀ j < n, μ' (dst+j) = μ (a+j)*μ (b+j)) ∧
        SameOutside μ μ' dst n) := by sorry
