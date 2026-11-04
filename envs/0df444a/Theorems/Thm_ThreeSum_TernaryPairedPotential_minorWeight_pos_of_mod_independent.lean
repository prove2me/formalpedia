-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedPotential_minorWeight_pos_of_mod_independent
-- name    : ThreeSum.TernaryPairedPotential.minorWeight_pos_of_mod_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:30.460178+00:00
-- url     : https://prove2.me/theorems/ed9ea6ae-9ccf-461a-bf4d-e4065b0684ca
-- title:
--   Ternary Paired Potential: minor Weight pos of mod independent
-- statement:
--   The Ternary Paired Potential construction uses the minor Weight pos of mod independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L52-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L52-L64

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformRank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedPotential
open Finset Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K] [DecidableEq K]

theorem ThreeSum.TernaryPairedPotential.minorWeight_pos_of_mod_independent {d Λ : ℕ}
    (A : Matrix (Fin d) (Fin Λ) ℤ) (ρ : ℤ →+* K)
    (hA : LinearIndependent K (fun i j => ρ (A i j))) :
    0 < minorWeight A := by sorry
