-- Prove2me | Theorems.Thm_Value_stSumOut
-- name    : Value.stSumOut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:23:57.077325+00:00
-- url     : https://prove2.me/theorems/d8f1b219-6202-42df-b2ab-cdcc280e16f0
-- title:
--   Value: st Sum Out
-- statement:
--   «Each θ_{a,b} occurs only in f_{a,b} and f_{b,a}, and Σ_{θ_{a,b}∈{0,1}^{c_{a,b}}} f_{a,b}(z_a,
--   θ_{a,b}) f_{b,a}(z_b, θ_{a,b}) = Ψ_{a,b}(z_a, z_b)»: the sum over all θ of the product over the
--   pairs is the product over the pairs of the sums, each sum is Ψ_{a,b}(z_a, z_b), and the pairs in the
--   same group and the pairs in different groups are all pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Sums.lean#L103-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Sums.lean#L103-L115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Sums
set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Finset Eight.SecNetworks
variable {g K : ℕ}

theorem Value.stSumOut : StSumOut := by sorry
