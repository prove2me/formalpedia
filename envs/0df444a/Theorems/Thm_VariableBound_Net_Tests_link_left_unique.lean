-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_link_left_unique
-- name    : VariableBound.Net.Tests.link_left_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:03:10.743424+00:00
-- url     : https://prove2.me/theorems/23ab4a13-b03e-4674-8c40-e431d35d2d68
-- title:
--   Tests: link left unique
-- statement:
--   The upper end of a link determines its lower end.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L56-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L56-L62

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

theorem VariableBound.Net.Tests.link_left_unique {e a a' b : ℕ} (hb : b ≤ g) (h : linkB g n D e a b = true) (h' : linkB g n D e a' b = true) : a = a' := by sorry
