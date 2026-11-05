-- Prove2me | Theorems.Thm_PiecesCounted_answerOf_eq
-- name    : PiecesCounted.answerOf_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:21:33.951677+00:00
-- url     : https://prove2.me/theorems/56188a67-c33c-40d0-bf27-8ff397c68bbb
-- title:
--   Pieces Counted: answer Of eq
-- statement:
--   `answerOf` gives the right answer when the padding string has 2^{cλ} units.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Padded.lean#L63-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Padded.lean#L63-L107

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCounted_PadThen
import Definitions.Def_PiecesCounted_PaddedData
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Padded
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.answerOf_eq {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} {shift : ℕ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val)
    {g : List Unit × Question} {a : Answer} (hg : (ofPadded P A c shift).oracle g = some a) : answerOf P val shift (g, List.replicate (2 ^ (c * g.1.length)) ()) = a := by sorry
