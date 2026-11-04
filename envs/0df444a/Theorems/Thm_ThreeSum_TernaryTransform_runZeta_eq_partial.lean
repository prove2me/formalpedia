-- Prove2me | Theorems.Thm_ThreeSum_TernaryTransform_runZeta_eq_partial
-- name    : ThreeSum.TernaryTransform.runZeta_eq_partial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:18:17.299992+00:00
-- url     : https://prove2.me/theorems/ef39102b-57df-4b3a-a5c6-dd92494dc969
-- title:
--   Ternary Transform: run Zeta eq partial
-- statement:
--   The Ternary Transform construction uses the run Zeta eq partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTransform.lean#L90-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTransform.lean#L90-L97

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryTransform
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTransform
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler

theorem ThreeSum.TernaryTransform.runZeta_eq_partial {N : ℕ} (coords : List (Fin N)) (h : coords.Nodup)
    (f : TritWord N → ℤ) : runZeta coords f = stageSum coords.toFinset f := by sorry
