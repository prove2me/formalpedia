-- Prove2me | Theorems.Thm_Potential_rectangle_return
-- name    : Potential.rectangle_return
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:52:09.39757+00:00
-- url     : https://prove2.me/theorems/a47d9f99-4f3c-4ab6-aa77-103e99283de8
-- title:
--   Potential: rectangle return
-- statement:
--   The Potential construction uses the rectangle return property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L203-L207
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L203-L207

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

theorem Potential.rectangle_return (s : Profile A) (i j : I) (hij : i ≠ j)
    (a : A i) (b : A j) :
    Function.update (Function.update (Function.update s i a) j b) i (s i) =
      Function.update s j b := by sorry
