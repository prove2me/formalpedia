-- Prove2me | Theorems.Thm_SNumbers_Complexification_conj_smul
-- name    : SNumbers.Complexification.conj_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:02:50.226899+00:00
-- url     : https://prove2.me/theorems/314e507a-ee9a-4362-9e10-80504968795c
-- title:
--   Complexification: conj smul
-- statement:
--   Conjugation is conjugate-linear: `conj (c • u) = conj c • conj u`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L278-L281
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L278-L281

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

theorem SNumbers.Complexification.conj_smul (c : ℂ) (u : Complexification H) :
    conj (c • u) = (starRingEnd ℂ c) • conj u := by sorry
