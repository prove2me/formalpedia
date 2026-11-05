-- Prove2me | Theorems.Thm_P2M_Groundwork_Network_merge___lt_75b913e72a8f
-- name    : P2M_Groundwork_Network_merge___lt_75b913e72a8f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:49.931763+00:00
-- url     : https://prove2.me/theorems/aa0f7e78-4807-4d37-91a5-35dadea35394
-- title:
--   P2 M Groundwork Network merge   lt 75b913e72a8f: P2 M Groundwork Network merge   lt 75b913e72a8f
-- statement:
--   The interaction of two classes G < G' is the product of the interactions of their members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L197-L205
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L197-L205

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network

theorem P2M_Groundwork_Network_merge___lt_75b913e72a8f [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    {G G' : J'} (h : G < G') (z z' : J → σ) :
    (N.merge χ s₀ t₀).Ψ G G' z z' = ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.Ψ p.1 p.2 (z p.1) (z' p.2) := by sorry

alias «Groundwork».«Network».«merge_Ψ_lt» := P2M_Groundwork_Network_merge___lt_75b913e72a8f
