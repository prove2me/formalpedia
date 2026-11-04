-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedPotential_minorWeight_le
-- name    : ThreeSum.TernaryPairedPotential.minorWeight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:05:55.416884+00:00
-- url     : https://prove2.me/theorems/fa89840b-dc3b-4daf-8143-e83149a3485c
-- title:
--   Ternary Paired Potential: minor Weight le
-- statement:
--   The Ternary Paired Potential construction uses the minor Weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L127-L134
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L127-L134

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

theorem ThreeSum.TernaryPairedPotential.minorWeight_le {d Λ : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ) (b : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ b) :
    minorWeight A ≤ Λ^d*(d.factorial*b^d)^2 := by sorry
