-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_obAt_inj
-- name    : VariableBound.Net.Basic.obAt_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:04:18.826853+00:00
-- url     : https://prove2.me/theorems/f70c0985-ac82-4bb2-b571-d13c32ebd74a
-- title:
--   Basic: ob At inj
-- statement:
--   For well-formed data (WfD), two places below the number of objects that hold the same triple are
--   equal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L111-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L111-L113

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

theorem VariableBound.Net.Basic.obAt_inj (hW : WfD k n D) {o o' : ℕ} (h : o < (objs D).length) (h' : o' < (objs D).length) (he : obAt D o = obAt D o') : o = o' := by sorry
