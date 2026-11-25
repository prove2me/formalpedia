-- Prove2me | Theorems.Thm_Potential_endpoint_cons
-- name    : Potential.endpoint_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:51:51.661815+00:00
-- url     : https://prove2.me/theorems/2ef3ba96-ac87-4991-8a02-f6bacda9aefd
-- title:
--   Potential: endpoint cons
-- statement:
--   The Potential construction uses the endpoint cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L62-L65
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L62-L65

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

theorem Potential.endpoint_cons {I : Type*} {A : I → Type*} [DecidableEq I]
    (s : Profile A) (m : Move A) (ms : List (Move A)) :
    endpoint s (m :: ms) = endpoint (Function.update s m.1 m.2) ms := by sorry
