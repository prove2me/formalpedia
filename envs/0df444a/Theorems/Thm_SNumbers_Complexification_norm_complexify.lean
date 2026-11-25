-- Prove2me | Theorems.Thm_SNumbers_Complexification_norm_complexify
-- name    : SNumbers.Complexification.norm_complexify
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:34:14.359803+00:00
-- url     : https://prove2.me/theorems/e49ecca4-bc8c-4626-adce-b86a44cb390e
-- title:
--   Complexification: norm complexify
-- statement:
--   The complexification preserves the operator norm.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L365-L371
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L365-L371

module
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic.Module
public import Definitions.Def_BasicResults_Spectral_Complexification
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open RCLike Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
open SNumbers
open SNumbers.Complexification
variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]

theorem SNumbers.Complexification.norm_complexify (S : H₁ →L[ℝ] H₂) : ‖complexify S‖ = ‖S‖ := by sorry
