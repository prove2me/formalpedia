-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_sum_length_tst_le
-- name    : VariableBound.Net.Tests.sum_length_tst_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:01:43.192419+00:00
-- url     : https://prove2.me/theorems/3e677712-6b16-497a-8a20-2fd647a54a30
-- title:
--   Tests: sum length tst le
-- statement:
--   Step 3, «The total»: T_κ = Σ_(a < b < g) t_(a,b,κ) is at most k − 1 + κ times the number of
--   objects of kind κ, if Φ has clauses of at most k literals (`WfD`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L205-L208
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L205-L208

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

theorem VariableBound.Net.Tests.sum_length_tst_le (hW : WfD k n D) (κ : ℕ) :
    ∑ b ∈ range g, ∑ a ∈ range b, (tst g n D a b κ).length ≤ (k - 1 + κ) * #((range (objs D).length).filter fun o => (obAt D o).1 = κ) := by sorry
