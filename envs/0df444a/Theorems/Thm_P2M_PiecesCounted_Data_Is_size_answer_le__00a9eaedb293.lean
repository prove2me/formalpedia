-- Prove2me | Theorems.Thm_P2M_PiecesCounted_Data_Is_size_answer_le__00a9eaedb293
-- name    : P2M_PiecesCounted_Data_Is_size_answer_le__00a9eaedb293
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:19:54.146971+00:00
-- url     : https://prove2.me/theorems/a51e4be4-0638-4aa0-9eb9-e0d209bffd46
-- title:
--   P2 M Pieces Counted Data Is size answer le  00a9eaedb293: P2 M Pieces Counted Data Is size answer le  00a9eaedb293
-- statement:
--   An answer: at most (2λ)^c·(2λ)^c + 4·(2λ)^c + 2^{cλ} + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L187-L193
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L187-L193

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_Basic
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Sizes
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog

theorem P2M_PiecesCounted_Data_Is_size_answer_le__00a9eaedb293 {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) {g : List Unit × Question} {a : Answer} (hg : D.oracle g = some a) :
    size a ≤ (2 * g.1.length) ^ c * (2 * g.1.length) ^ c + 4 * (2 * g.1.length) ^ c + 2 ^ (c * g.1.length) + 2 := by sorry

alias «PiecesCounted».«Data».«Is».«size_answer_le'» := P2M_PiecesCounted_Data_Is_size_answer_le__00a9eaedb293
