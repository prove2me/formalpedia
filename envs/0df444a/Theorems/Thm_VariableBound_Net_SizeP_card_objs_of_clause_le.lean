-- Prove2me | Theorems.Thm_VariableBound_Net_SizeP_card_objs_of_clause_le
-- name    : VariableBound.Net.SizeP.card_objs_of_clause_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:47:30.544896+00:00
-- url     : https://prove2.me/theorems/1ce334c3-bae6-44a7-a3c9-6c19995674c3
-- title:
--   Size P: card objs of clause le
-- statement:
--   Step 3, «The parameters»: a clause E «gives one mark of kind 0 and load(E) marks of kind 1»: at
--   most 1 + load(E) objects have the clause number e (for well-formed data, `WfD`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L94-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeP.lean#L94-L112

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Net_SizeB
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_SizeP
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}

theorem VariableBound.Net.SizeP.card_objs_of_clause_le (hW : WfD k n D) (e : ℕ) : #((range (objs D).length).filter fun o => (obAt D o).2.1 = e) ≤ 1 + colD D e := by sorry
