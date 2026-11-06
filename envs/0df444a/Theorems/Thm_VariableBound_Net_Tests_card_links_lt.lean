-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_card_links_lt
-- name    : VariableBound.Net.Tests.card_links_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:46:25.051989+00:00
-- url     : https://prove2.me/theorems/b92ea1a7-2f2b-4981-a0a1-42fa373f7adc
-- title:
--   Tests: card links lt
-- statement:
--   An object that touches a node has fewer links than touched nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L75-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L75-L102

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

theorem VariableBound.Net.Tests.card_links_lt (e : ℕ) (h : ∃ a < g, tchB g n D a e = true) :
    #(((range g) ×ˢ (range g)).filter fun p => linkB g n D e p.1 p.2 = true) < #((range g).filter fun a => tchB g n D a e = true) := by sorry
