-- Prove2me | Theorems.Thm_PiecesCounted_Data_Is_cap_le
-- name    : PiecesCounted.Data.Is.cap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:19:19.619081+00:00
-- url     : https://prove2.me/theorems/25dda693-6749-4ed1-b649-d3e23d66cc4e
-- title:
--   Is: cap le
-- statement:
--   c^row_i, c^col_i ≤ cλ + 4λ, from the bound of (b).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L70-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L70-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Basic
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Sizes
import Theorems.Thm_Groundwork_Prog_NetE_cap_le

set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog

theorem PiecesCounted.Data.Is.cap_le {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) {lam : ℕ} (hl : 1 ≤ lam) {i : ℤ} (hi : i ∈ (D.fam lam).I) (tr : Bool) : D.cap lam tr i ≤ c * lam + 4 * lam := by sorry
