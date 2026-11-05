-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_sum_map_range
-- name    : VariableBound.Net.Tests.sum_map_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:01:17.475557+00:00
-- url     : https://prove2.me/theorems/ad0d93b9-623d-4e30-83bc-c4420100caeb
-- title:
--   Tests: sum map range
-- statement:
--   The sum of a list indexed by the numbers below R, as a sum over a finite set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L126-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L126-L129

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_Stepped_sum_map_range
import Theorems.Thm_PaddedDescent_F_Mark_Prof_sum_map_range
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Tests.sum_map_range (f : ℕ → ℕ) (R : ℕ) : ((List.range R).map f).sum = ∑ i ∈ range R, f i := by sorry
