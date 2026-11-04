-- Prove2me | Theorems.Thm_ThreeSumApsp_WordRam_IsDataStructure_mono
-- name    : ThreeSumApsp.WordRam.IsDataStructure.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:01:42.843793+00:00
-- url     : https://prove2.me/theorems/a56e5324-2d9a-4c6e-9229-b755c1101657
-- title:
--   Is Data Structure: mono
-- statement:
--   `IsDataStructure` stays true for a larger slope, a smaller set of instances and larger
--   bounds.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L108-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Machine/Solving.lean#L108-L122

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr)
open Filter

theorem ThreeSumApsp.WordRam.IsDataStructure.mono {P Q : List Instr} {qI qJ qOut : ℤ} {b b' : ℕ} {extra : List ℤ}
    {dom dom' : ThinPair → Prop} {Tp Sp Tq Tp' Sp' Tq' : ThinPair → ℝ}
    (h : IsDataStructure P Q qI qJ qOut b extra dom Tp Sp Tq) (hb : b ≤ b')
    (hdom : ∀ x, dom' x → dom x) (hTp : ∀ x, dom' x → Tp x ≤ Tp' x)
    (hSp : ∀ x, dom' x → Sp x ≤ Sp' x) (hTq : ∀ x, dom' x → Tq x ≤ Tq' x) :
    IsDataStructure P Q qI qJ qOut b' extra dom' Tp' Sp' Tq' := by sorry
