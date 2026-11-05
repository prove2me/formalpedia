-- Prove2me | Theorems.Thm_WidthK_Step_lay_nextN_of_ne
-- name    : WidthK.Step.lay_nextN_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:41:09.441847+00:00
-- url     : https://prove2.me/theorems/223dc440-c16d-4ccf-91e9-9cd1271819b4
-- title:
--   Step: lay next N of ne
-- statement:
--   At a size other than r, N keeps the clauses that contain no added set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L79-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Step.lean#L79-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_SparsifyWidthK_Step
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
open WidthK
open Finset Groundwork Groundwork.Sparsify
variable {α : Type*} [DecidableEq α]
open WidthK.Step
variable {d : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}

theorem WidthK.Step.lay_nextN_of_ne (hA : AddK d F A r) {i : ℕ} (hi : i ≠ r) :
    lay (nextN N A) i = (lay N i).filter fun C => ∀ D ∈ A, ¬ D ⊆ C := by sorry
