-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_sum_lt_eq_sum_product
-- name    : VariableBound.Net.Tests.sum_lt_eq_sum_product
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:46:27.648207+00:00
-- url     : https://prove2.me/theorems/4a97ad53-ea38-4140-b4bb-fa3f15683677
-- title:
--   Tests: sum lt eq sum product
-- statement:
--   The sum over a' < a < g as a sum over all pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L160-L168
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L160-L168

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Tests.sum_lt_eq_sum_product (F : ℕ → ℕ → ℕ) (g : ℕ) :
    ∑ a ∈ range g, ∑ a' ∈ range a, F a' a = ∑ p ∈ (range g) ×ˢ (range g), if p.1 < p.2 then F p.1 p.2 else 0 := by sorry
