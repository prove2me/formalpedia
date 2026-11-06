-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_link_right_unique
-- name    : VariableBound.Net.Tests.link_right_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:46:47.410861+00:00
-- url     : https://prove2.me/theorems/dc8de6c4-7bbd-4a52-a931-89943961c095
-- title:
--   Tests: link right unique
-- statement:
--   The lower end of a link determines its upper end.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L65-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L65-L71

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

theorem VariableBound.Net.Tests.link_right_unique {e a b b' : ℕ} (hb : b < g) (hb' : b' < g) (h : linkB g n D e a b = true) (h' : linkB g n D e a b' = true) : b = b' := by sorry
