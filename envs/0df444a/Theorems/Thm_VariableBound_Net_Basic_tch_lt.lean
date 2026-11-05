-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_tch_lt
-- name    : VariableBound.Net.Basic.tch_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:44:18.53549+00:00
-- url     : https://prove2.me/theorems/7d35cd1a-b8db-47b9-abef-3a44311d5a8f
-- title:
--   Basic: tch lt
-- statement:
--   For g > 0 and well-formed data (WfD), a node that an object touches is below g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L170-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L170-L173

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

theorem VariableBound.Net.Basic.tch_lt (hg : 0 < g) (hW : WfD k n D) {o a : ℕ} (ho : o < (objs D).length) (h : tchB g n D a o = true) : a < g := by sorry
