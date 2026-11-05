-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_clOf_wf
-- name    : VariableBound.Net.Basic.clOf_wf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:44:56.616449+00:00
-- url     : https://prove2.me/theorems/a7de9cf8-485d-4c09-b074-52617dd0952f
-- title:
--   Basic: cl Of wf
-- statement:
--   For well-formed data (WfD), the clause of an object has 1 to k literals on variables below n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L87-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L87-L89

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

theorem VariableBound.Net.Basic.clOf_wf (hW : WfD k n D) {o : ℕ} (h : o < (objs D).length) :
    clOf D o ≠ [] ∧ (clOf D o).length ≤ k ∧ ∀ l ∈ clOf D o, l.1 < n := by sorry
