-- Prove2me | Theorems.Thm_SNumbers_Complexification_complexify_fst
-- name    : SNumbers.Complexification.complexify_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:46.115542+00:00
-- url     : https://prove2.me/theorems/a7c12dba-4b80-410b-92d2-489661c9c8f1
-- title:
--   Complexification: complexify fst
-- statement:
--   The Complexification construction uses the complexify fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L349-L350
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L349-L350

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

theorem SNumbers.Complexification.complexify_fst (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    (complexify S u).1 = S u.1 := by sorry

attribute [defeq] SNumbers.Complexification.complexify_fst
