-- Prove2me | Theorems.Thm_Potential_maskedProfile_insert
-- name    : Potential.maskedProfile_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:55:32.179251+00:00
-- url     : https://prove2.me/theorems/7fd45fdd-7dcd-5080-90ef-e47276d55909
-- title:
--   Potential: masked Profile insert
-- statement:
--   The Potential construction uses the masked Profile insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L127-L135
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L127-L135

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

theorem Potential.maskedProfile_insert {I : Type*} {A : I → Type*} [DecidableEq I]
    (base s : Profile A) (S : Finset I) (i : I) :
    maskedProfile base (insert i S) s =
      Function.update (maskedProfile base S s) i (s i) := by sorry
