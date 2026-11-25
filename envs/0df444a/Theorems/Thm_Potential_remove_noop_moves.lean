-- Prove2me | Theorems.Thm_Potential_remove_noop_moves
-- name    : Potential.remove_noop_moves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:55:54.829892+00:00
-- url     : https://prove2.me/theorems/0fabccf5-f993-52f9-beb8-a770ed59c2ec
-- title:
--   Potential: remove noop moves
-- statement:
--   No-op moves can be removed without changing either endpoint or integral.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L257-L275
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L257-L275

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

theorem Potential.remove_noop_moves (u : Payoff A) (s : Profile A) (ms : List (Move A)) :
    ∃ ns : List (Move A), ActualPath s ns ∧ endpoint s ns = endpoint s ms ∧
      pathIntegral u s ns = pathIntegral u s ms := by sorry
