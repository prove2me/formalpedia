-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
-- name    : ThreeSum.TernaryCoverRegularity.reindex_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:52:19.033186+00:00
-- url     : https://prove2.me/theorems/e807056b-3d5b-4be4-bec7-01724fe471db
-- title:
--   Ternary Cover Regularity: reindex symm
-- statement:
--   The Ternary Cover Regularity construction uses the reindex symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L55-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverRegularity.lean#L55-L58

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

theorem ThreeSum.TernaryCoverRegularity.reindex_symm (σ : Equiv.Perm (Fin L)) (w : TritWord L) :
    reindex σ.symm (reindex σ w) = w := by sorry
