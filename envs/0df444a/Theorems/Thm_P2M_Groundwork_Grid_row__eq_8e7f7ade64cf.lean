-- Prove2me | Theorems.Thm_P2M_Groundwork_Grid_row__eq_8e7f7ade64cf
-- name    : P2M_Groundwork_Grid_row__eq_8e7f7ade64cf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:26.781308+00:00
-- url     : https://prove2.me/theorems/712720fa-5e73-479b-9180-50e7479d7db2
-- title:
--   P2 M Groundwork Grid row  eq 8e7f7ade64cf: P2 M Groundwork Grid row  eq 8e7f7ade64cf
-- statement:
--   The interaction of two rows is factorised by rowTop and rowBot over rowΘ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/RowNet.lean#L44-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/RowNet.lean#L44-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Grid
import Definitions.Def_Groundwork_Grid_RowNet
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [Fintype ρ] [LinearOrder ρ]

theorem P2M_Groundwork_Grid_row__eq_8e7f7ade64cf {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect ρ γ → Cut α τ} (h : ∀ ω, (C ω).Factors (G ω)) (t₀ : τ)
    (a b : ρ) (z z' : RowSt ρ γ α) :
    rowΨ G a b z z' = ∑ θ ∈ rowΘ C t₀ a b, rowTop C a b z θ * rowBot C a b z' θ := by sorry

alias «Groundwork».«Grid».«rowΨ_eq» := P2M_Groundwork_Grid_row__eq_8e7f7ade64cf
