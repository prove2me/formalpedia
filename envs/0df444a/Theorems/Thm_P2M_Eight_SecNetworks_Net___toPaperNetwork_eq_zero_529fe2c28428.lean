-- Prove2me | Theorems.Thm_P2M_Eight_SecNetworks_Net___toPaperNetwork_eq_zero_529fe2c28428
-- name    : P2M_Eight_SecNetworks_Net___toPaperNetwork_eq_zero_529fe2c28428
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:28:20.961614+00:00
-- url     : https://prove2.me/theorems/78006553-63b8-4f6f-94dc-e0d56e764547
-- title:
--   P2 M Eight Sec Networks Net   to Paper Network eq zero 529fe2c28428: P2 M Eight Sec Networks Net   to Paper Network eq zero 529fe2c28428
-- statement:
--   Off S_a × S_b, the Ψ_{a,b} that proof/networks/Paper defines from the factors is 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L118-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L118-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_LemGrouping
set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset Stepped
open Eight.SecNetworks.Net
variable {g : ℕ} (N : Net g)
variable {N} {P B : ℕ}

theorem P2M_Eight_SecNetworks_Net___toPaperNetwork_eq_zero_529fe2c28428 {a b : Fin g} {z z' : List Bool} (hz : ¬(z ∈ N.S a ∧ z' ∈ N.S b)) : N.toPaperNetwork.Ψ a b z z' = 0 := by sorry

alias «Eight».«SecNetworks».«Net».«Ψ_toPaperNetwork_eq_zero» := P2M_Eight_SecNetworks_Net___toPaperNetwork_eq_zero_529fe2c28428
