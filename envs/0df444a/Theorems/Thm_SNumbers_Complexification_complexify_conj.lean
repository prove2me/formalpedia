-- Prove2me | Theorems.Thm_SNumbers_Complexification_complexify_conj
-- name    : SNumbers.Complexification.complexify_conj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:49.320948+00:00
-- url     : https://prove2.me/theorems/20bbab07-2c7a-4b50-b08d-c3109504e67b
-- title:
--   Complexification: complexify conj
-- statement:
--   `Sℂ` commutes with conjugation (this is what it means for `Sℂ` to be "real").
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L360-L362
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L360-L362

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

theorem SNumbers.Complexification.complexify_conj (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    complexify S (conj u) = conj (complexify S u) := by sorry
