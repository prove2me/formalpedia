-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_sum_length_tst_node_le
-- name    : VariableBound.Net.Tests.sum_length_tst_node_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:46:37.030231+00:00
-- url     : https://prove2.me/theorems/2e2cd79c-a14a-4051-8e14-f228c06a1204
-- title:
--   Tests: sum length tst node le
-- statement:
--   Step 3, «The parameters»: «an object has at most two tests at a». All the strings that a node a
--   < g shares with the other nodes together have at most twice as many bits as objects touch a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L265-L289
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L265-L289

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Tests.sum_length_tst_node_le {a : ℕ} (ha : a < g) :
    ∑ b ∈ (range g).erase a, ∑ κ ∈ range 2, (tst g n D a b κ).length ≤ 2 * (tch g n D a).length := by sorry
