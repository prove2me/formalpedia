-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_card_kind_zero
-- name    : VariableBound.Net.Tests.card_kind_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:54:41.225914+00:00
-- url     : https://prove2.me/theorems/fe23642a-3086-414f-b67e-da73aede15dd
-- title:
--   Tests: card kind zero
-- statement:
--   There are m objects of kind 0 (for well-formed data, `WfD`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L211-L221
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L211-L221

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
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Tests.card_kind_zero (hW : WfD k n D) : #((range (objs D).length).filter fun o => (obAt D o).1 = 0) = D.1.length := by sorry
