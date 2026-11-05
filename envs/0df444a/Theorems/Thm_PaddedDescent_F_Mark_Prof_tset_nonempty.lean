-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_tset_nonempty
-- name    : PaddedDescent.F.Mark.Prof.tset_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:55:29.591315+00:00
-- url     : https://prove2.me/theorems/47879207-5907-44a6-846d-5ae62cca2295
-- title:
--   Prof: tset nonempty
-- statement:
--   A clause touches some node below g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L126-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L126-L133

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_Digits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_PaddedDescent_F_MarkProf
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Prof
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.Mark.Prof.tset_nonempty {k g n : ℕ} {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) :
    (tset g n Ls e).Nonempty := by sorry
