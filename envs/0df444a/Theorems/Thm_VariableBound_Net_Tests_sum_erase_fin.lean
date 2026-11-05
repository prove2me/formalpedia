-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_sum_erase_fin
-- name    : VariableBound.Net.Tests.sum_erase_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:01:30.421764+00:00
-- url     : https://prove2.me/theorems/2594c184-3148-46b8-81c8-d7fb75709dd5
-- title:
--   Tests: sum erase fin
-- statement:
--   A sum over the other nodes, as a sum over numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L132-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L132-L139

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

theorem VariableBound.Net.Tests.sum_erase_fin (a : Fin g) (F : ℕ → ℕ) : ∑ b ∈ (univ : Finset (Fin g)).erase a, F b.val = ∑ b ∈ (range g).erase a.val, F b := by sorry
