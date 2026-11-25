-- Prove2me | Theorems.Thm_SNumbers_Complexification_complexify_snd
-- name    : SNumbers.Complexification.complexify_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:30:54.189961+00:00
-- url     : https://prove2.me/theorems/55f159ff-d417-490a-b98e-782d2d6712cb
-- title:
--   Complexification: complexify snd
-- statement:
--   The Complexification construction uses the complexify snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L351-L352
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L351-L352

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

theorem SNumbers.Complexification.complexify_snd (S : H₁ →L[ℝ] H₂) (u : Complexification H₁) :
    (complexify S u).2 = S u.2 := by sorry

attribute [defeq] SNumbers.Complexification.complexify_snd
