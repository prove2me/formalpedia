-- Prove2me | Theorems.Thm_Potential_rectangle_vertices_nodup
-- name    : Potential.rectangle_vertices_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:58:33.220638+00:00
-- url     : https://prove2.me/theorems/c33ad4aa-2f7e-5be4-a043-09cb4ec1ed4b
-- title:
--   Potential: rectangle vertices nodup
-- statement:
--   A nondegenerate two-player rectangle is a simple four-step closed path.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L373-L396
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L373-L396

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

theorem Potential.rectangle_vertices_nodup (s : Profile A) (i j : I) (hij : i ≠ j)
    (a : A i) (b : A j) (ha : a ≠ s i) (hb : b ≠ s j) :
    (vertices s [⟨i, a⟩, ⟨j, b⟩, ⟨i, s i⟩, ⟨j, s j⟩]).dropLast.Nodup := by sorry
