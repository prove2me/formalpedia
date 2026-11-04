-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedPotential_rowWeight_le
-- name    : ThreeSum.TernaryPairedPotential.rowWeight_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:32.505735+00:00
-- url     : https://prove2.me/theorems/1207609d-641e-4151-8d88-1b8be2115158
-- title:
--   Ternary Paired Potential: row Weight le
-- statement:
--   The Ternary Paired Potential construction uses the row Weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L136-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L136-L139

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

theorem ThreeSum.TernaryPairedPotential.rowWeight_le {ι : Type*} [Fintype ι] {Λ : ℕ}
    (A : ι → Fin Λ → ℤ) (b : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ b) :
    rowWeight A ≤ Λ^(Fintype.card ι)*((Fintype.card ι).factorial*b^(Fintype.card ι))^2 := by sorry
