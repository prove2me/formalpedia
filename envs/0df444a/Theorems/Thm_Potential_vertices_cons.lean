-- Prove2me | Theorems.Thm_Potential_vertices_cons
-- name    : Potential.vertices_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:58:03.308801+00:00
-- url     : https://prove2.me/theorems/fcb19984-7041-4b37-bf0f-bcf071dedda0
-- title:
--   Potential: vertices cons
-- statement:
--   The Potential construction uses the vertices cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L346-L350
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L346-L350

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

theorem Potential.vertices_cons (s : Profile A) (m : Move A) (ms : List (Move A)) :
    vertices s (m :: ms) = s :: vertices (Function.update s m.1 m.2) ms := by sorry
