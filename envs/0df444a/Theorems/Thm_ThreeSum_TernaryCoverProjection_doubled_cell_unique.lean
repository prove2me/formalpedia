-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverProjection_doubled_cell_unique
-- name    : ThreeSum.TernaryCoverProjection.doubled_cell_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:13.898088+00:00
-- url     : https://prove2.me/theorems/173a81bd-8c05-4c4c-8656-f45a642fe2eb
-- title:
--   Ternary Cover Projection: doubled cell unique
-- statement:
--   The Ternary Cover Projection construction uses the doubled cell unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L120-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L120-L126

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryCoverProjection.doubled_cell_unique (swap : Bool) (a b c d : Fin 3)
    (hab : a.val + b.val ≤ 2) (hcd : c.val + d.val ≤ 2)
    (heq : doubledCode swap a b = doubledCode swap c d)
    (hmark : doubledMark swap a b ↔ doubledMark swap c d) :
    a = c ∧ b = d := by sorry
