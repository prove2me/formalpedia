-- Prove2me | Theorems.Thm_P2M_Eight_SecNetworks_Net___toPaperNetwork_89d84f9cfc58
-- name    : P2M_Eight_SecNetworks_Net___toPaperNetwork_89d84f9cfc58
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:20:58.294458+00:00
-- url     : https://prove2.me/theorems/dfb9ba93-cc98-4e8a-95d5-69addc3c323d
-- title:
--   P2 M Eight Sec Networks Net   to Paper Network 89d84f9cfc58: P2 M Eight Sec Networks Net   to Paper Network 89d84f9cfc58
-- statement:
--   On S_a × S_b, the Ψ_{a,b} that proof/networks/Paper defines from the factors is the Ψ_{a,b} of
--   N, because (f_{a,b}, f_{b,a}) is a factorization of Ψ_{a,b} (Definition 2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L109-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L109-L115

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

theorem P2M_Eight_SecNetworks_Net___toPaperNetwork_89d84f9cfc58 (h : N.Is P B) {a b : Fin g} (hab : a ≠ b) {z z' : List Bool} (hz : z ∈ N.S a) (hz' : z' ∈ N.S b) :
    N.toPaperNetwork.Ψ a b z z' = N.Ψ a b z z' := by sorry

alias «Eight».«SecNetworks».«Net».«Ψ_toPaperNetwork» := P2M_Eight_SecNetworks_Net___toPaperNetwork_89d84f9cfc58
