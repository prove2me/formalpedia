-- Prove2me | Theorems.Thm_ThreeSum_LightResidues_residue_cast
-- name    : ThreeSum.LightResidues.residue_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:25:32.314203+00:00
-- url     : https://prove2.me/theorems/07002d6b-c83f-4249-9233-40be4481f85c
-- title:
--   Light Residues: residue cast
-- statement:
--   The Light Residues construction uses the residue cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidues.lean#L21-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightResidues.lean#L21-L24

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightResidues
set_option autoImplicit false
open ThreeSum ThreeSum.LightResidues
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightResidues.residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ℤ) = (c * x) % (p : ℤ) := by sorry
