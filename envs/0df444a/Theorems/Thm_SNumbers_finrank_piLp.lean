-- Prove2me | Theorems.Thm_SNumbers_finrank_piLp
-- name    : SNumbers.finrank_piLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:01:42.486315+00:00
-- url     : https://prove2.me/theorems/b55ed803-6180-4d6a-bc1e-763b47c1a33a
-- title:
--   SNumbers: finrank pi Lp
-- statement:
--   The dimension of `ℓ^p_k = PiLp p (Fin k → 𝕜)` is `k`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L65-L67
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/PiLpCoordinates.lean#L65-L67

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
omit [Fact (1 ≤ p)]

theorem SNumbers.finrank_piLp (k : ℕ) :
    Module.finrank 𝕜 (PiLp p (fun _ : Fin k => 𝕜)) = k := by sorry
