-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_kind_zero_iff
-- name    : VariableBound.Net.Basic.kind_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:41.414197+00:00
-- url     : https://prove2.me/theorems/1268d2ea-fec9-48d4-8ad3-0bb58efd811d
-- title:
--   Basic: kind zero iff
-- statement:
--   For well-formed data (WfD), an object is a clause iff it is among the first m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L132-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L132-L141

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

theorem VariableBound.Net.Basic.kind_zero_iff (hW : WfD k n D) {o : ℕ} (h : o < (objs D).length) : (obAt D o).1 = 0 ↔ o < D.1.length := by sorry
