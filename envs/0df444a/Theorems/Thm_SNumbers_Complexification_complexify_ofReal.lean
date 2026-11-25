-- Prove2me | Theorems.Thm_SNumbers_Complexification_complexify_ofReal
-- name    : SNumbers.Complexification.complexify_ofReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:50.250302+00:00
-- url     : https://prove2.me/theorems/34144b78-0ced-4cee-848e-cc94f7e5f7d9
-- title:
--   Complexification: complexify of Real
-- statement:
--   `Sℂ` agrees with `S` on the real subspace: `Sℂ (x + i·0) = (S x) + i·0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L355-L357
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L355-L357

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

theorem SNumbers.Complexification.complexify_ofReal (S : H₁ →L[ℝ] H₂) (x : H₁) :
    complexify S (ofReal x) = ofReal (S x) := by sorry
