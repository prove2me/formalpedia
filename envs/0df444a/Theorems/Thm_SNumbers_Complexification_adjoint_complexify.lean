-- Prove2me | Theorems.Thm_SNumbers_Complexification_adjoint_complexify
-- name    : SNumbers.Complexification.adjoint_complexify
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:35:13.205572+00:00
-- url     : https://prove2.me/theorems/cba9b768-4bb4-46d5-8b11-d41fcf49154a
-- title:
--   Complexification: adjoint complexify
-- statement:
--   Complexification commutes with taking adjoints: `(Sℂ)* = (S*)ℂ`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L378-L385
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L378-L385

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
variable [CompleteSpace H₁] [CompleteSpace H₂]

theorem SNumbers.Complexification.adjoint_complexify (S : H₁ →L[ℝ] H₂) :
    ContinuousLinearMap.adjoint (complexify S) = complexify (ContinuousLinearMap.adjoint S) := by sorry
