-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_card_links_at_le
-- name    : VariableBound.Net.Tests.card_links_at_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:46:53.313093+00:00
-- url     : https://prove2.me/theorems/f84e960f-d50a-4c60-bc48-fa27a024b211
-- title:
--   Tests: card links at le
-- statement:
--   At a node a, an object has at most two links, and none if it does not touch a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L237-L261
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L237-L261

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Tests.card_links_at_le {a : ℕ} (ha : a < g) (e : ℕ) :
    #(((range g).erase a).filter fun b => linkB g n D e (min a b) (max a b) = true) ≤ if tchB g n D a e = true then 2 else 0 := by sorry
