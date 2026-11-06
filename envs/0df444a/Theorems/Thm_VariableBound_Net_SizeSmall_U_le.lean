-- Prove2me | Theorems.Thm_VariableBound_Net_SizeSmall_U_le
-- name    : VariableBound.Net.SizeSmall.U_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:50:31.588882+00:00
-- url     : https://prove2.me/theorems/1f8e0854-45f4-427c-a583-927c0c898da3
-- title:
--   Size Small: U le
-- statement:
--   With the empty list of checks, the number of all tests is at most (k − 1)·m, for ψ well formed
--   (`WfD`); as every test costs at most one bit, U ≤ 2(k − 1)·m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeSmall.lean#L43-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeSmall.lean#L43-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_SizeP
import Definitions.Def_VariableBound_Net_SizeSmall
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeSmall
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (qv occ)
variable {k g n Δ : ℕ}

theorem VariableBound.Net.SizeSmall.U_le {ψ : Fml} (hW : WfD k n (ψ, [])) (y : ℕ) (fl : Bool) : (netDN g (ctx g n (ψ, []) y fl)).U ≤ 2 * (k - 1) * ψ.length := by sorry
