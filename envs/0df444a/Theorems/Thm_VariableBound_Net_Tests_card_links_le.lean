-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_card_links_le
-- name    : VariableBound.Net.Tests.card_links_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:46:39.604876+00:00
-- url     : https://prove2.me/theorems/bab913f9-aee5-4319-bd16-7ba2c71bd6f8
-- title:
--   Tests: card links le
-- statement:
--   Step 3: «an object of kind κ has at most k − 1 + κ tests»; here with the number of literals of
--   its clause in place of k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L113-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L113-L121

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
import Theorems.Thm_PaddedDescent_F_Mark_Prof_card_links_le
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Tests.card_links_le (e : ℕ) :
    #(((range g) ×ˢ (range g)).filter fun p => linkB g n D e p.1 p.2 = true) ≤ (clOf D e).length + (obAt D e).1 - 1 := by sorry
