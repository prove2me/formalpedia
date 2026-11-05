-- Prove2me | Theorems.Thm_P2M_ClauseBound_Grid_abs_rowNet___lt_05db5343e15b
-- name    : P2M_ClauseBound_Grid_abs_rowNet___lt_05db5343e15b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:02.660603+00:00
-- url     : https://prove2.me/theorems/464f7feb-135d-42d4-b366-d0c00b8fd132
-- title:
--   P2 M Clause Bound Grid abs row Net   lt 05db5343e15b: P2 M Clause Bound Grid abs row Net   lt 05db5343e15b
-- statement:
--   The interaction of two rows is a product of at most d² values of the functions at the
--   rectangles.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L159-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L159-L165

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

theorem P2M_ClauseBound_Grid_abs_rowNet___lt_05db5343e15b {d L b n : ℕ} (hγ : Fintype.card γ = d) (R : Inst (ρ × γ) α)
    {G : Rect ρ γ → α → α → α → α → ℤ} (C : Rect ρ γ → Cut α τ) (t₀ : τ) (hF : ∀ ω, (C ω).Factors (G ω))
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) (hn : d ^ 2 * b ≤ n) {a c : ρ} (h : a < c) (z z' : RowSt ρ γ α) :
    |(rowNet R C t₀ L).Ψ a c z z'| ≤ 2 ^ n := by sorry

alias «ClauseBound».«Grid».«abs_rowNet_Ψ_lt» := P2M_ClauseBound_Grid_abs_rowNet___lt_05db5343e15b
