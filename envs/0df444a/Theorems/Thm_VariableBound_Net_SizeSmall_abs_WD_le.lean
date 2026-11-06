-- Prove2me | Theorems.Thm_VariableBound_Net_SizeSmall_abs_WD_le
-- name    : VariableBound.Net.SizeSmall.abs_WD_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T07:14:31.584114+00:00
-- url     : https://prove2.me/theorems/7f92c7bf-675c-41c6-a3f7-21f16cad330a
-- title:
--   Size Small: abs WD le
-- statement:
--   With the empty list of checks, |W_a| ≤ 2^1 for every node, profile, flag and word: condition (ii)
--   with B = 1. (In fact W_a is 0, 1 or −1.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeSmall.lean#L35-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeSmall.lean#L35-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_SizeP
import Definitions.Def_VariableBound_Net_SizeSmall
import Theorems.Thm_VariableBound_Net_SizeB_abs_WD_le

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeSmall
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (qv occ)
variable {k g n Δ : ℕ}

theorem VariableBound.Net.SizeSmall.abs_WD_le (ψ : Fml) (y : ℕ) (fl : Bool) (a : ℕ) (z : List Bool) : |WD g n (ψ, []) y fl a z| ≤ 2 ^ 1 := by sorry
