-- Prove2me | Theorems.Thm_VariableBound_Net_Tests_capD_comm
-- name    : VariableBound.Net.Tests.capD_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:01:29.287665+00:00
-- url     : https://prove2.me/theorems/cfd6a712-cbda-4a7c-84c5-1b9d7ad0cff7
-- title:
--   Tests: cap D comm
-- statement:
--   c_(a,b) = c_(b,a).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L294-L295
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Tests.lean#L294-L295

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

theorem VariableBound.Net.Tests.capD_comm (y a b : ℕ) : capD g n D y a b = capD g n D y b a := by sorry
