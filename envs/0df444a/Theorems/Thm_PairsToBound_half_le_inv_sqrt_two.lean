-- Prove2me | Theorems.Thm_PairsToBound_half_le_inv_sqrt_two
-- name    : PairsToBound.half_le_inv_sqrt_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:58:48.904091+00:00
-- url     : https://prove2.me/theorems/77f8233e-b1b7-4cb1-94da-8cfe7afd66af
-- title:
--   Pairs To Bound: half le inv sqrt two
-- statement:
--   1/2 ≤ 1/√2 < 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Pairs.lean#L125-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Pairs.lean#L125-L130

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

theorem PairsToBound.half_le_inv_sqrt_two : (1 : ℝ) / 2 ≤ 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 < 1 := by sorry
