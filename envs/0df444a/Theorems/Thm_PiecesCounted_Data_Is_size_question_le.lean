-- Prove2me | Theorems.Thm_PiecesCounted_Data_Is_size_question_le
-- name    : PiecesCounted.Data.Is.size_question_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:58:59.453462+00:00
-- url     : https://prove2.me/theorems/cdf5bbb4-8ca3-49d4-9d1b-8cc1852009be
-- title:
--   Is: size question le
-- statement:
--   A question that has an answer, with λ in unary, has size at most (2λ)^c + 14λ + 2cλ + 11.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L86-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L86-L119

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

theorem PiecesCounted.Data.Is.size_question_le {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) {g : List Unit × Question} {a : Answer} (hg : D.oracle g = some a) :
    size g ≤ (2 * g.1.length) ^ c + 14 * g.1.length + 2 * (c * g.1.length) + 11 := by sorry
