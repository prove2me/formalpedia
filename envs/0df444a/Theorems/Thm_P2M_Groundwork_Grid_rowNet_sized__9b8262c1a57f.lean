-- Prove2me | Theorems.Thm_P2M_Groundwork_Grid_rowNet_sized__9b8262c1a57f
-- name    : P2M_Groundwork_Grid_rowNet_sized__9b8262c1a57f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:49.467563+00:00
-- url     : https://prove2.me/theorems/b236108c-4be0-4a63-9992-948ddd5d183a
-- title:
--   P2 M Groundwork Grid row Net sized  9b8262c1a57f: P2 M Groundwork Grid row Net sized  9b8262c1a57f
-- statement:
--   The shape and the magnitudes of the row network when every rectangle is charged at most 2mL
--   bits, m ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Size.lean#L191-L216
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Size.lean#L191-L216

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

theorem P2M_Groundwork_Grid_rowNet_sized__9b8262c1a57f {g L m B b : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = g) (hγ : Fintype.card γ = g)
    (hα : Fintype.card α = 2 ^ L) (R : Inst (ρ × γ) α) (hR : ∀ w h, |R w h| ≤ 2 ^ B)
    {G : Rect ρ γ → α → α → α → α → ℤ} (C : Rect ρ γ → Cut α τ) (t₀ : τ)
    (hF : ∀ ω, (C ω).Factors (G ω)) (hcard : ∀ ω, #(C ω).lab ≤ 2 ^ (C ω).cap) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L)
    (htop : ∀ ω x y θ, |(C ω).top x y θ| ≤ 2 ^ b) (hbot : ∀ ω u v θ, |(C ω).bot u v θ| ≤ 2 ^ b)
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) :
    (rowNet R C t₀ L).Sized (m * (g ^ 3 * L)) (g * B + g ^ 2 * b) := by sorry

alias «Groundwork».«Grid».«rowNet_sized'» := P2M_Groundwork_Grid_rowNet_sized__9b8262c1a57f
