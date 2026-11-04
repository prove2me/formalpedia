-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedPotential_minor_natAbs_le
-- name    : ThreeSum.TernaryPairedPotential.minor_natAbs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:10:47.325847+00:00
-- url     : https://prove2.me/theorems/461d8966-28ae-491d-880d-e47b81bc6b81
-- title:
--   Ternary Paired Potential: minor nat Abs le
-- statement:
--   The Ternary Paired Potential construction uses the minor nat Abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L108-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L108-L119

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

theorem ThreeSum.TernaryPairedPotential.minor_natAbs_le {d Λ : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ) (b : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ b) (f : Fin d → Fin Λ) :
    (A.submatrix id f).det.natAbs ≤ d.factorial*b^d := by sorry
