-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCell_program_inverse_meets
-- name    : ThreeSum.LightTernaryCell.program_inverse_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:41.852217+00:00
-- url     : https://prove2.me/theorems/018fe0c6-90ad-4f74-947a-d682afbd260d
-- title:
--   Light Ternary Cell: program inverse meets
-- statement:
--   The Light Ternary Cell construction uses the program inverse meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCell.lean#L116-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCell.lean#L116-L124

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_LightTernaryCell
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCell
open Light ThreeSum.TernaryQuery
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryCell.program_inverse_meets {μ : ℕ → ℤ} {a0 a1 a2 U : ℕ}
    (q : Fin 3) (f : Fin 3 → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (h0 : a0 < lim.space) (h1 : a1 < lim.space) (h2 : a2 < lim.space)
    (hr0 : μ a0 = f 0) (hr1 : μ a1 = f 1) (hr2 : μ a2 = f 2)
    (hf : ∀ e, |f e| ≤ U) (hword : 4 * (U : ℤ) + 3 ≤ lim.word) :
    Meets lim program 1 d [q.val,a0,a1,a2] μ time
      (fun r μ' => r = inverseDigit f q ∧ μ' = μ) := by sorry
