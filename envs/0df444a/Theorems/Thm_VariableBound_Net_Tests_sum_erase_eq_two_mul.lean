-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_sum_erase_eq_two_mul
-- name    : VariableBound.Net.Tests.sum_erase_eq_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:46:42.089482+00:00
-- url     : https://prove2.me/theorems/365abff8-32e8-46dc-9725-2c8659dda9b8
-- title:
--   Tests: sum erase eq two mul
-- statement:
--   A symmetric table summed over the ordered pairs of different numbers below g is twice its sum
--   over the pairs a' < a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L143-L156
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L143-L156

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

theorem VariableBound.Net.Tests.sum_erase_eq_two_mul (F : ℕ → ℕ → ℕ) (hF : ∀ a b, F a b = F b a) (g : ℕ) :
    ∑ a ∈ range g, ∑ b ∈ (range g).erase a, F a b = 2 * ∑ a ∈ range g, ∑ a' ∈ range a, F a' a := by sorry
