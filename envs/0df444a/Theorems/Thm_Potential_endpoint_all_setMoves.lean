-- Prove2me | Theorems.Thm_Potential_endpoint_all_setMoves
-- name    : Potential.endpoint_all_setMoves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:57:56.752674+00:00
-- url     : https://prove2.me/theorems/57af93bf-3a7f-4740-839a-27f335459e7c
-- title:
--   Potential: endpoint all set Moves
-- statement:
--   The Potential construction uses the endpoint all set Moves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L300-L303
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L300-L303

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max
public import Definitions.Def_MondererShapley_Solution
set_option autoImplicit true
@[expose] public section
public section
open Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]

theorem Potential.endpoint_all_setMoves [Fintype I] (base target : Profile A) :
    endpoint base (Finset.univ.toList.map (fun i => (⟨i, target i⟩ : Move A))) = target := by sorry
