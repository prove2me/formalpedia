-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverProjection_differenceCode_eq_of_field
-- name    : ThreeSum.TernaryCoverProjection.differenceCode_eq_of_field
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:33.449501+00:00
-- url     : https://prove2.me/theorems/8a8e240c-fd5e-4535-92f4-9230166b1e8c
-- title:
--   Ternary Cover Projection: difference Code eq of field
-- statement:
--   The Ternary Cover Projection construction uses the difference Code eq of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L32-L41
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverProjection.lean#L32-L41

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Definitions.Def_Submission_ThreeSum_TernaryCoverProjection
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverProjection
open Finset TernaryJointType TernaryCoverLocal

theorem ThreeSum.TernaryCoverProjection.differenceCode_eq_of_field {p : ℕ} (hp : 4 < p) (a b c d : Fin 3)
    (heq : (a.val : ZMod p) - (b.val : ZMod p) =
      (c.val : ZMod p) - (d.val : ZMod p)) :
    differenceCode a b = differenceCode c d := by sorry
