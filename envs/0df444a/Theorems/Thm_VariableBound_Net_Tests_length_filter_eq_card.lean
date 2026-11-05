-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_length_filter_eq_card
-- name    : VariableBound.Net.Tests.length_filter_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:04:19.733278+00:00
-- url     : https://prove2.me/theorems/4e6f5072-dd5a-48cc-8e47-cd1bdcc019af
-- title:
--   Tests: length filter eq card
-- statement:
--   The length of a filtered list of the numbers below M, as the number of elements of a finite set.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L105-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L105-L109

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

theorem VariableBound.Net.Tests.length_filter_eq_card (M : ℕ) (p : ℕ → Bool) : ((List.range M).filter p).length = #((range M).filter fun e => p e = true) := by sorry
