-- Prove2me | Theorems.Thm_P2M_Groundwork_Network_merge___472728bb004e
-- name    : P2M_Groundwork_Network_merge___472728bb004e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:52.693349+00:00
-- url     : https://prove2.me/theorems/0aab9cfb-4f09-414c-bb7f-0c1581b16ef6
-- title:
--   P2 M Groundwork Network merge   472728bb004e: P2 M Groundwork Network merge   472728bb004e
-- statement:
--   The interaction of two classes is the product of the interactions of their members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L208-L215
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L208-L215

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

theorem P2M_Groundwork_Network_merge___472728bb004e [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ) (t₀ : τ)
    {G G' : J'} (h : G ≠ G') (z z' : J → σ) :
    (N.merge χ s₀ t₀).Ψ G G' z z' = ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.Ψ p.1 p.2 (z p.1) (z' p.2) := by sorry

alias «Groundwork».«Network».«merge_Ψ» := P2M_Groundwork_Network_merge___472728bb004e
