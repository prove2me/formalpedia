-- Prove2me | Theorems.Thm_PiecesCounted_assumeAlg_runs_two
-- name    : PiecesCounted.assumeAlg_runs_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:01:06.620783+00:00
-- url     : https://prove2.me/theorems/3519eeb2-b36b-445c-b960-ec7fb22ea370
-- title:
--   Pieces Counted: assume Alg runs two
-- statement:
--   The run with a second run of Alg.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L179-L181
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesCounted/Trimmed.lean#L179-L181

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

theorem PiecesCounted.assumeAlg_runs_two {Alg : Stepped (List Unit × Question) Answer} {g g' : List Unit × Question} {a₀ a : Answer} {t t' S S' : ℕ} (h1 : Alg.Runs (firstQ g) t S a₀)
    (h2 : afterFirst (g, a₀) = .inr g') (h3 : Alg.Runs g' t' S' a) : (assumeAlg Alg).Runs g (t + 1 + t') (max (size g + S) (S' + 1) + 1) a := by sorry
