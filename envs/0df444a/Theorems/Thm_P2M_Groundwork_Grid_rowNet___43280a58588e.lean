-- Prove2me | Theorems.Thm_P2M_Groundwork_Grid_rowNet___43280a58588e
-- name    : P2M_Groundwork_Grid_rowNet___43280a58588e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:48.386027+00:00
-- url     : https://prove2.me/theorems/c7624611-c926-4a9a-a297-95e1950f10e2
-- title:
--   P2 M Groundwork Grid row Net   43280a58588e: P2 M Groundwork Grid row Net   43280a58588e
-- statement:
--   The interaction of the row network is rowΨ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/RowNet.lean#L56-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/RowNet.lean#L56-L60

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

theorem P2M_Groundwork_Grid_rowNet___43280a58588e {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect ρ γ → Cut α τ} (h : ∀ ω, (C ω).Factors (G ω))
    (R : Inst (ρ × γ) α) (t₀ : τ) (L : ℕ) {a b : ρ} (hab : a < b) (z z' : RowSt ρ γ α) :
    (rowNet R C t₀ L).Ψ a b z z' = rowΨ G a b z z' := by sorry

alias «Groundwork».«Grid».«rowNet_Ψ» := P2M_Groundwork_Grid_rowNet___43280a58588e
