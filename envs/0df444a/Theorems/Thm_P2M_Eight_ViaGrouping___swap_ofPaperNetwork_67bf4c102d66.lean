-- Prove2me | Theorems.Thm_P2M_Eight_ViaGrouping___swap_ofPaperNetwork_67bf4c102d66
-- name    : P2M_Eight_ViaGrouping___swap_ofPaperNetwork_67bf4c102d66
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:04:30.484069+00:00
-- url     : https://prove2.me/theorems/f2fee459-1014-48a8-b130-16be67c2cd87
-- title:
--   P2 M Eight Via Grouping   swap of Paper Network 67bf4c102d66: P2 M Eight Via Grouping   swap of Paper Network 67bf4c102d66
-- statement:
--   The Ψ that proof/networks/Paper defines from the factors is symmetric: Ψ_{b,a}(z', z) =
--   Ψ_{a,b}(z, z').
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L45-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L45-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}

theorem P2M_Eight_ViaGrouping___swap_ofPaperNetwork_67bf4c102d66 (N : Paper.Network (Fin g) (List Bool) (List Bool)) (a b : Fin g) (z z' : List Bool) : N.Ψ b a z' z = N.Ψ a b z z' := by sorry

alias «Eight».«ViaGrouping».«Ψ_swap_ofPaperNetwork» := P2M_Eight_ViaGrouping___swap_ofPaperNetwork_67bf4c102d66
