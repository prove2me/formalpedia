-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_cl_lt
-- name    : VariableBound.Net.Basic.cl_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:18:51.376191+00:00
-- url     : https://prove2.me/theorems/2ffa9bc8-b71d-406f-902b-40f12f7b5133
-- title:
--   Basic: cl lt
-- statement:
--   For well-formed data (WfD), the clause of an object is a clause of ψ: its number is below m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L77-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L77-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Basic
open Groundwork Groundwork.Prog PaddedDescent.F
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Basic.cl_lt (hW : WfD k n D) {o : ℕ} (h : o < (objs D).length) : (obAt D o).2.1 < D.1.length := by sorry
