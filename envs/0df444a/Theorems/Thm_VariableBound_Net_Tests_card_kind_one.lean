-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_card_kind_one
-- name    : VariableBound.Net.Tests.card_kind_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:01:46.542394+00:00
-- url     : https://prove2.me/theorems/ad3bc61a-7d1f-46c9-9b7d-88b9c29d702f
-- title:
--   Tests: card kind one
-- statement:
--   There are I = Σ_j |Λ_j| objects of kind 1 (for well-formed data, `WfD`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L224-L232
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L224-L232

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Tests.card_kind_one (hW : WfD k n D) : #((range (objs D).length).filter fun o => (obAt D o).1 = 1) = (D.2.map List.length).sum := by sorry
