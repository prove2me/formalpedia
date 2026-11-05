-- Prove2me | Theorems.Thm_P2M_Groundwork_Grid___eq_product_67598949e673
-- name    : P2M_Groundwork_Grid___eq_product_67598949e673
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:20.039954+00:00
-- url     : https://prove2.me/theorems/1c938faa-b675-4321-bb91-759dddd8b911
-- title:
--   P2 M Groundwork Grid   eq product 67598949e673: P2 M Groundwork Grid   eq product 67598949e673
-- statement:
--   The rectangles, sorted by pairs of rows.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L100-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L100-L101

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]

theorem P2M_Groundwork_Grid___eq_product_67598949e673 : Ω ρ γ = pairs ρ ×ˢ (univ.filter fun k : γ × γ => k.1 < k.2) := by sorry

alias «Groundwork».«Grid».«Ω_eq_product» := P2M_Groundwork_Grid___eq_product_67598949e673
