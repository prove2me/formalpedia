-- Prove2me | Theorems.Thm_SNumbers_le_gelfandNumber
-- name    : SNumbers.le_gelfandNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:22:55.860673+00:00
-- url     : https://prove2.me/theorems/eb918d3a-7203-428e-87ef-f9ac7feef331
-- title:
--   SNumbers: le gelfand Number
-- statement:
--   Lower bound for the Gelfand number: if `f` is a lower bound for the restriction
--   deviation over every admissible (closed, codimension `≤ n`) subspace, then `f ≤ c_n(S)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L133-L138
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L133-L138

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.le_gelfandNumber {S : X →L[𝕜] Y} {n : ℕ} {f : ℝ}
    (h : ∀ M : Submodule 𝕜 X, IsClosed (M : Set X) →
        Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal) → f ≤ deviationFromRestriction S M) :
    f ≤ gelfandNumber S n := by sorry
