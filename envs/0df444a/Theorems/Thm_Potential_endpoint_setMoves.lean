-- Prove2me | Theorems.Thm_Potential_endpoint_setMoves
-- name    : Potential.endpoint_setMoves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:57:59.200978+00:00
-- url     : https://prove2.me/theorems/b3204119-057e-4853-a097-d98feeae7c00
-- title:
--   Potential: endpoint set Moves
-- statement:
--   Visiting the listed players once gives the target coordinates on that list.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L288-L298
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L288-L298

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

theorem Potential.endpoint_setMoves (base target : Profile A) (is : List I) (j : I) :
    endpoint base (is.map (fun i => (⟨i, target i⟩ : Move A))) j =
      if j ∈ is then target j else base j := by sorry
