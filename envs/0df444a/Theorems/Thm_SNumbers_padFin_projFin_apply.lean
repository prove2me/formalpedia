-- Prove2me | Theorems.Thm_SNumbers_padFin_projFin_apply
-- name    : SNumbers.padFin_projFin_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:45:07.937567+00:00
-- url     : https://prove2.me/theorems/f7613f6b-25c7-4c3c-8ece-8f00f25fb4f1
-- title:
--   SNumbers: pad Fin proj Fin apply
-- statement:
--   Embedding the first `n` coordinates back gives the **coordinate truncation**
--   `Pₙ = padFin ∘ projFin` on `ℓ^p_m`: it keeps the first `n` coordinates and zeros
--   the rest.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L98-L103
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L98-L103

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

theorem SNumbers.padFin_projFin_apply (h : n ≤ m) (x : PiLp p (fun _ : Fin m => 𝕜)) (i : Fin m) :
    (padFin (projFin (p := p) h x)) i = if (i : ℕ) < n then x i else 0 := by sorry
