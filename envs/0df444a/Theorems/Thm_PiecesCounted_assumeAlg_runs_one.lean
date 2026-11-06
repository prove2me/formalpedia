-- Prove2me | Theorems.Thm_PiecesCounted_assumeAlg_runs_one
-- name    : PiecesCounted.assumeAlg_runs_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:11.115731+00:00
-- url     : https://prove2.me/theorems/c2a08301-0117-4344-9784-3e64e090632d
-- title:
--   Pieces Counted: assume Alg runs one
-- statement:
--   The run in which the answer is there after the first run of Alg.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L174-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L174-L176

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Sizes
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_GeneralPieces_Trim_Prog
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Trimmed
set_option autoImplicit false
section
section
open PiecesCounted
open Finset Groundwork Groundwork.Prog ClauseBound.Alg

theorem PiecesCounted.assumeAlg_runs_one {Alg : Stepped (List Unit × Question) Answer} {g : List Unit × Question} {a₀ a : Answer} {t S : ℕ} (h1 : Alg.Runs (firstQ g) t S a₀) (h2 : afterFirst (g, a₀) = .inl a) :
    (assumeAlg Alg).Runs g (t + 1 + 1) (max (size g + S) (max (size a) (size a) + 1 + 1) + 1) a := by sorry
