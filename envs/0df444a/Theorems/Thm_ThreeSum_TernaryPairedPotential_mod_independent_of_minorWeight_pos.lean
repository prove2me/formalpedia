-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedPotential_mod_independent_of_minorWeight_pos
-- name    : ThreeSum.TernaryPairedPotential.mod_independent_of_minorWeight_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:48.738821+00:00
-- url     : https://prove2.me/theorems/cf5226e6-7da8-4689-82f5-c5caf0f7d8b3
-- title:
--   Ternary Paired Potential: mod independent of minor Weight pos
-- statement:
--   The Ternary Paired Potential construction uses the mod independent of minor Weight pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L69-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L69-L87

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

theorem ThreeSum.TernaryPairedPotential.mod_independent_of_minorWeight_pos {d Λ p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin d) (Fin Λ) ℤ) (hw : 0 < minorWeight A)
    (hsmall : ∀ f : Fin d → Fin Λ, (A.submatrix id f).det.natAbs < p) :
    LinearIndependent (ZMod p) (fun i j => (A i j : ZMod p)) := by sorry
