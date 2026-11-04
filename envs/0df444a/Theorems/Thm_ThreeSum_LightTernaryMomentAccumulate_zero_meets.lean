-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentAccumulate_zero_meets
-- name    : ThreeSum.LightTernaryMomentAccumulate.zero_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:54:17.565468+00:00
-- url     : https://prove2.me/theorems/a6023929-4f0d-4736-9cc3-f07ac9e580a2
-- title:
--   Light Ternary Moment Accumulate: zero meets
-- statement:
--   The Light Ternary Moment Accumulate construction uses the zero meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentAccumulate.lean#L48-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentAccumulate.lean#L48-L62

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentAccumulate
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryMomentAccumulate.zero_meets {p matrix terms count : ℕ}
    (hmain : P[p]?=some fillBody) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : matrix+terms*count≤lim.space) :
    Meets lim P p d [matrix,terms*count,0] μ (fillTime (terms*count))
      (fun _ ν => (∀ k<terms, ∀ i<count, ν (matrix+k*count+i)=0) ∧
        SameOutside μ ν matrix (terms*count)) := by sorry
