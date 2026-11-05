-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_capD_eq
-- name    : VariableBound.Net.Tests.capD_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:54:48.110403+00:00
-- url     : https://prove2.me/theorems/e98cb6a8-7ce6-46f6-930b-cc294f09468d
-- title:
--   Tests: cap D eq
-- statement:
--   c_(a,b) as a sum over the two kinds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L298-L299
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L298-L299

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Basic
import Definitions.Def_VariableBound_Net_Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_VariableBound_Net_Tests
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Tests
open Groundwork Groundwork.Prog Finset
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Tests.capD_eq (y a b : ℕ) : capD g n D y a b = ∑ κ ∈ range 2, cw (tst g n D a b κ).length (mu g D y a b κ) := by sorry
