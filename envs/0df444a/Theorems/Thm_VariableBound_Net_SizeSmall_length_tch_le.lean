-- Prove2me | Theorems.Thm_VariableBound_Net_SizeSmall_length_tch_le
-- name    : VariableBound.Net.SizeSmall.length_tch_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T07:13:47.733305+00:00
-- url     : https://prove2.me/theorems/c0043e54-5ffa-4a05-806e-f92042d082b7
-- title:
--   Size Small: length tch le
-- statement:
--   With the empty list of checks, at most ⌈n/g⌉·Δ objects touch a node, if g > 0, ψ is well formed
--   (`WfD`) and every variable occurs in at most Δ clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeSmall.lean#L29-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/SizeSmall.lean#L29-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_SizeP
import Definitions.Def_VariableBound_Net_SizeSmall
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_Mark_Deg_length_tch_le
import Theorems.Thm_VariableBound_Net_SizeP_length_tch_le
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeSmall
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (qv occ)
variable {k g n Δ : ℕ}

theorem VariableBound.Net.SizeSmall.length_tch_le {ψ : Fml} (hg : 0 < g) (hW : WfD k n (ψ, [])) (hΔ : ∀ v, (occ ψ v).length ≤ Δ) (a : ℕ) : (tch g n (ψ, []) a).length ≤ qv g n * Δ := by sorry
