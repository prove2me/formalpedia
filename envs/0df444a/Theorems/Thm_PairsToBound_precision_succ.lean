-- Prove2me | Theorems.Thm_PairsToBound_precision_succ
-- name    : PairsToBound.precision_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:40.547399+00:00
-- url     : https://prove2.me/theorems/1b73c5ca-48f4-4454-8cc7-8d59e52dcc7d
-- title:
--   Pairs To Bound: precision succ
-- statement:
--   For 1/2 ≤ ρ < 1 and x₀ ≥ 18, ℓ ↦ ℓ + 1 is a precision for the numbers e_ℓ of display (40), by
--   part (a) of Theorem A.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Pairs.lean#L134-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Pairs.lean#L134-L138

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Defs
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Rec_PartB
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_PairsToBound_Pairs
set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen GeneralPieces MainTheoremForms

theorem PairsToBound.precision_succ {ρ : ℝ} {x₀ : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) : ∃ C : ℕ, Precision (e ρ x₀) RecursionWithPieces.prec C := by sorry
