-- Prove2me | Theorems.Thm_P2M_PiecesCounted_Data_Is_size_question_le__c8f9744f479a
-- name    : P2M_PiecesCounted_Data_Is_size_question_le__c8f9744f479a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:19:47.522203+00:00
-- url     : https://prove2.me/theorems/c91b5a0a-a53a-4185-bb55-ca9f4ab4591c
-- title:
--   P2 M Pieces Counted Data Is size question le  c8f9744f479a: P2 M Pieces Counted Data Is size question le  c8f9744f479a
-- statement:
--   A question that has an answer: at most 8·(2λ)^c + 2·2^{cλ} + 11.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L179-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Sizes.lean#L179-L184

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

theorem P2M_PiecesCounted_Data_Is_size_question_le__c8f9744f479a {D : Data} {ρ : ℝ} {c : ℕ} (h : D.Is ρ c) {g : List Unit × Question} {a : Answer} (hg : D.oracle g = some a) :
    size g ≤ 8 * (2 * g.1.length) ^ c + 2 * 2 ^ (c * g.1.length) + 11 := by sorry

alias «PiecesCounted».«Data».«Is».«size_question_le'» := P2M_PiecesCounted_Data_Is_size_question_le__c8f9744f479a
