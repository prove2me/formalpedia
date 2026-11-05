-- Prove2me | Theorems.Thm_P2M_Groundwork_Network___comm_f75ed8fe8218
-- name    : P2M_Groundwork_Network___comm_f75ed8fe8218
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:28:04.211131+00:00
-- url     : https://prove2.me/theorems/8eda8cdc-6bb0-4434-ae9a-a680e72baea3
-- title:
--   P2 M Groundwork Network   comm f75ed8fe8218: P2 M Groundwork Network   comm f75ed8fe8218
-- statement:
--   The interaction of a pair, read from the other side.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L76-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L76-L79

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

theorem P2M_Groundwork_Network___comm_f75ed8fe8218 [LinearOrder J] (N : Network J σ τ) (a b : J) (z z' : σ) : N.Ψ a b z z' = N.Ψ b a z' z := by sorry

alias «Groundwork».«Network».«Ψ_comm» := P2M_Groundwork_Network___comm_f75ed8fe8218
