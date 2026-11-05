-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_clOf_mem
-- name    : VariableBound.Net.Basic.clOf_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:44:08.593095+00:00
-- url     : https://prove2.me/theorems/acd75fed-3363-446f-ae3d-dffe99b610d4
-- title:
--   Basic: cl Of mem
-- statement:
--   For well-formed data (WfD), the clause of an object is a member of ψ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L83-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L83-L84

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

theorem VariableBound.Net.Basic.clOf_mem (hW : WfD k n D) {o : ℕ} (h : o < (objs D).length) : clOf D o ∈ D.1 := by sorry
