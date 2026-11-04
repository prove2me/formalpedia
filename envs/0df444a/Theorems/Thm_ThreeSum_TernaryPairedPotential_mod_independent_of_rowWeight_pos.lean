-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedPotential_mod_independent_of_rowWeight_pos
-- name    : ThreeSum.TernaryPairedPotential.mod_independent_of_rowWeight_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:52:20.995199+00:00
-- url     : https://prove2.me/theorems/bf632168-3496-453c-8d1a-619a8662b348
-- title:
--   Ternary Paired Potential: mod independent of row Weight pos
-- statement:
--   The Ternary Paired Potential construction uses the mod independent of row Weight pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L98-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedPotential.lean#L98-L106

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

theorem ThreeSum.TernaryPairedPotential.mod_independent_of_rowWeight_pos {ι : Type*} [Fintype ι] {Λ p : ℕ} [Fact p.Prime]
    (A : ι → Fin Λ → ℤ) (hw : 0 < rowWeight A)
    (hsmall : ∀ f : Fin (Fintype.card ι) → Fin Λ,
      (Matrix.submatrix (fun i => A ((Fintype.equivFin ι).symm i)) id f).det.natAbs < p) :
    LinearIndependent (ZMod p) (fun i j => (A i j : ZMod p)) := by sorry
