-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedPotential_exists_nonsingular_column_selection
-- name    : ThreeSum.TernaryPairedPotential.exists_nonsingular_column_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:15.935062+00:00
-- url     : https://prove2.me/theorems/277db236-0760-4f6c-be6b-c7f25e6cfc83
-- title:
--   Ternary Paired Potential: exists nonsingular column selection
-- statement:
--   The Ternary Paired Potential construction uses the exists nonsingular column selection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L22-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L22-L47

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

theorem ThreeSum.TernaryPairedPotential.exists_nonsingular_column_selection {d Λ : ℕ}
    (A : Matrix (Fin d) (Fin Λ) K) (hA : LinearIndependent K A) :
    ∃ f : Fin d → Fin Λ, (A.submatrix id f).det ≠ 0 := by sorry
