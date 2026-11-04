-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedPotential_minor_small_of_entry_bound
-- name    : ThreeSum.TernaryPairedPotential.minor_small_of_entry_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:28.773603+00:00
-- url     : https://prove2.me/theorems/70bb7ddf-3091-456d-ac7f-c140cec6dc27
-- title:
--   Ternary Paired Potential: minor small of entry bound
-- statement:
--   The Ternary Paired Potential construction uses the minor small of entry bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L121-L125
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L121-L125

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

theorem ThreeSum.TernaryPairedPotential.minor_small_of_entry_bound {d Λ p : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ)
    (b : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ b) (hp : d.factorial*b^d < p) :
    ∀ f : Fin d → Fin Λ, (A.submatrix id f).det.natAbs < p := by sorry
