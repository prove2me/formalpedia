-- Prove2me | Theorems.Thm_SNumbers_le_kolmogorovNumber
-- name    : SNumbers.le_kolmogorovNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:06:44.676195+00:00
-- url     : https://prove2.me/theorems/d1a59bf5-a586-4688-aebd-5861848a5d56
-- title:
--   SNumbers: le kolmogorov Number
-- statement:
--   Lower bound for the Kolmogorov number: if `f` is a lower bound for the
--   quotient deviation over every admissible (dimension `≤ n`) subspace, then
--   `f ≤ d_n(S)`. Dual to `le_gelfandNumber`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L139-L144
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L139-L144

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
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

theorem SNumbers.le_kolmogorovNumber {S : X →L[𝕜] Y} {n : ℕ} {f : ℝ}
    (h : ∀ V : Submodule 𝕜 Y, Module.rank 𝕜 V ≤ (n : Cardinal) →
        f ≤ deviationFromSubspace S V) :
    f ≤ kolmogorovNumber S n := by sorry
