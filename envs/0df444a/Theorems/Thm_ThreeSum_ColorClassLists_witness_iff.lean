-- Prove2me | Theorems.Thm_ThreeSum_ColorClassLists_witness_iff
-- name    : ThreeSum.ColorClassLists.witness_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:45:18.514709+00:00
-- url     : https://prove2.me/theorems/6156ebcf-8675-4b9d-a1d6-b26687c27809
-- title:
--   Color Class Lists: witness iff
-- statement:
--   The Color Class Lists construction uses the witness iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L75-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorClassLists.lean#L75-L84

import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Definitions.Def_Submission_ThreeSum_LightColorIndex
import Definitions.Def_Submission_ThreeSum_ColorClassLists
set_option autoImplicit false
open ThreeSum ThreeSum.ColorClassLists
open LightClassFilter

theorem ThreeSum.ColorClassLists.witness_iff {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ) :
    witness p x ↔ Coloring.ThreeSetWitness
      (Coloring.values x (indexColor p) 0) (Coloring.values x (indexColor p) 1)
      (Coloring.negValues x (indexColor p)) := by sorry
