-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_clAt_wf
-- name    : PaddedDescent.F.Mark.Prof.clAt_wf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:11:28.77985+00:00
-- url     : https://prove2.me/theorems/792746fb-5921-41d6-a174-0b0e873e08f1
-- title:
--   Prof: cl At wf
-- statement:
--   A clause of well-formed layers has 1 to k literals on variables below n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L91-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L91-L107

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

theorem PaddedDescent.F.Mark.Prof.clAt_wf {k n : ℕ} {Ls : List Fml} (h : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) :
    (clAt Ls e).2 ≠ [] ∧ (clAt Ls e).2.length ≤ k ∧ ∀ l ∈ (clAt Ls e).2, l.1 < n := by sorry
