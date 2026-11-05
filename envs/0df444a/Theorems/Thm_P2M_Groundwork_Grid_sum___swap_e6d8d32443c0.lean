-- Prove2me | Theorems.Thm_P2M_Groundwork_Grid_sum___swap_e6d8d32443c0
-- name    : P2M_Groundwork_Grid_sum___swap_e6d8d32443c0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:57:31.802044+00:00
-- url     : https://prove2.me/theorems/28293821-e010-4c05-8b5b-b566200d4179
-- title:
--   P2 M Groundwork Grid sum   swap e6d8d32443c0: P2 M Groundwork Grid sum   swap e6d8d32443c0
-- statement:
--   A sum over the rectangles of the transposed grid.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Size.lean#L131-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Size.lean#L131-L139

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_Groundwork_Grid_Size
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype α] [DecidableEq α]

theorem P2M_Groundwork_Grid_sum___swap_e6d8d32443c0 (F : Rect ρ γ → ℕ) : ∑ ω ∈ Ω γ ρ, F (ω.2, ω.1) = ∑ ω ∈ Ω ρ γ, F ω := by sorry

alias «Groundwork».«Grid».«sum_Ω_swap» := P2M_Groundwork_Grid_sum___swap_e6d8d32443c0
