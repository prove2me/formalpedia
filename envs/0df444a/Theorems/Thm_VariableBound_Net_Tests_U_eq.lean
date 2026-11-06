-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_U_eq
-- name    : VariableBound.Net.Tests.U_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:01:54.831358+00:00
-- url     : https://prove2.me/theorems/abdc82e7-d83a-4bfd-8ea9-09147c92a703
-- title:
--   Tests: U eq
-- statement:
--   Step 3, «The total»: U = 2·Σ_({a,b}) c_(a,b), for the network of the profile y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L305-L310
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L305-L310

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

theorem VariableBound.Net.Tests.U_eq (y : ℕ) (fl : Bool) : (netDN g (ctx g n D y fl)).U = 2 * ∑ b ∈ range g, ∑ a ∈ range b, capD g n D y a b := by sorry
