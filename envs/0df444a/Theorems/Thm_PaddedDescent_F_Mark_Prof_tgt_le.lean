-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Prof_tgt_le
-- name    : PaddedDescent.F.Mark.Prof.tgt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:24:07.931017+00:00
-- url     : https://prove2.me/theorems/4cf88492-ec23-4936-9da4-02b4cb1f1d0b
-- title:
--   Prof: tgt le
-- statement:
--   The digits of P are at most the number of clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L326-L333
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkProf.lean#L326-L333

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

theorem PaddedDescent.F.Mark.Prof.tgt_le {g n : ℕ} {Ls : List Fml} {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length) (q : ℕ) :
    tgt g n Ls P q ≤ (cls Ls).length := by sorry
