-- Prove2me | Theorems.Thm_P2M_Groundwork_Grid_card___1355cab52dbf
-- name    : P2M_Groundwork_Grid_card___1355cab52dbf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:56:58.937711+00:00
-- url     : https://prove2.me/theorems/50726b77-fea7-4a4d-9246-3a67bd6497b6
-- title:
--   P2 M Groundwork Grid card   1355cab52dbf: P2 M Groundwork Grid card   1355cab52dbf
-- statement:
--   The number of rectangles is C(g,2)².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L164-L167
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L164-L167

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

theorem P2M_Groundwork_Grid_card___1355cab52dbf {g : ℕ} (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g) : #(Ω ρ γ) = g.choose 2 ^ 2 := by sorry

alias «Groundwork».«Grid».«card_Ω» := P2M_Groundwork_Grid_card___1355cab52dbf
