-- Prove2me | Theorems.Thm_Potential_maskedProfile_update_not_mem
-- name    : Potential.maskedProfile_update_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:55:22.165808+00:00
-- url     : https://prove2.me/theorems/79e2c671-7c3f-59e6-a4f1-90546c8b3205
-- title:
--   Potential: masked Profile update not mem
-- statement:
--   The Potential construction uses the masked Profile update not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L118-L125
-- source:
--   https://github.com/Arthur742Ramos/monderer-shapley-potential-lean/blob/bce2e989bc8243f938a34ac0f027b57063c71380/Solution.lean#L118-L125

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

theorem Potential.maskedProfile_update_not_mem {I : Type*} {A : I → Type*} [DecidableEq I]
    (base s : Profile A) (S : Finset I) (j : I) (a : A j) (hj : j ∉ S) :
    maskedProfile base S (Function.update s j a) = maskedProfile base S s := by sorry
