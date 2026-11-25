-- Prove2me | Theorems.Thm_SNumbers_padFin_apply
-- name    : SNumbers.padFin_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:39.538292+00:00
-- url     : https://prove2.me/theorems/6cc2f71f-6cff-48e6-aa98-843f6080479d
-- title:
--   SNumbers: pad Fin apply
-- statement:
--   The SNumbers construction uses the pad Fin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L92-L93
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L92-L93

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

theorem SNumbers.padFin_apply (y : PiLp p (fun _ : Fin n => 𝕜)) (i : Fin m) :
    (padFin (p := p) (m := m) y) i = if hi : (i : ℕ) < n then y ⟨i, hi⟩ else 0 := by sorry

attribute [defeq] SNumbers.padFin_apply
