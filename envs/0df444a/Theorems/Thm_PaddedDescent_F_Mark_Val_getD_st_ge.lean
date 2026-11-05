-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Val_getD_st_ge
-- name    : PaddedDescent.F.Mark.Val.getD_st_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:39.162713+00:00
-- url     : https://prove2.me/theorems/69f6634f-b02a-4739-b222-d84a5cecb3c0
-- title:
--   Val: get D st ge
-- statement:
--   The Val construction uses the get D st ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L512-L516
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkVal.lean#L512-L516

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Definitions.Def_PaddedDescent_F_MarkVal
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}

theorem PaddedDescent.F.Mark.Val.getD_st_ge (σ : ℕ → Bool) (P : Finset ℕ) (a : ℕ) {t : ℕ} (h : t < (tch g n Ls a).length) :
    (st g n Ls σ P a).getD (qv g n + t) false = decide ((tch g n Ls a)[t] ∈ P) := by sorry
