-- Prove2me | Theorems.Thm_SNumbers_padFin_castLE
-- name    : SNumbers.padFin_castLE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:18:51.792421+00:00
-- url     : https://prove2.me/theorems/53f8d12c-4275-4793-b4bc-a916cfab83ce
-- title:
--   SNumbers: pad Fin cast LE
-- statement:
--   The coordinate embedding agrees with the original on the embedded indices.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L133-L136
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L133-L136

module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_PiLpCoordinates
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SNumbers.padFin_castLE (h : n ≤ m) (y : PiLp p (fun _ : Fin n => 𝕜)) (j : Fin n) :
    (padFin (p := p) (m := m) y) (Fin.castLE h j) = y j := by sorry
