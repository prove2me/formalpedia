-- Prove2me | Theorems.Thm_SNumbers_Complexification_conj_eq_self_iff
-- name    : SNumbers.Complexification.conj_eq_self_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:12:17.423368+00:00
-- url     : https://prove2.me/theorems/f56cde38-b499-4970-9a65-dadba35e34d4
-- title:
--   Complexification: conj eq self iff
-- statement:
--   The elements fixed by conjugation are exactly the "real" ones, `x + i·0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L303-L311
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/BasicResults/Spectral/Complexification.lean#L303-L311

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

theorem SNumbers.Complexification.conj_eq_self_iff (u : Complexification H) : conj u = u ↔ ∃ x, u = ofReal x := by sorry
