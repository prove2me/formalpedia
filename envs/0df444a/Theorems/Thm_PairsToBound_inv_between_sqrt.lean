-- Prove2me | Theorems.Thm_PairsToBound_inv_between_sqrt
-- name    : PairsToBound.inv_between_sqrt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:56:06.763917+00:00
-- url     : https://prove2.me/theorems/30f23ba3-47de-42ae-9c45-95dd0d70b5cb
-- title:
--   Pairs To Bound: inv between sqrt
-- statement:
--   For a > 0 and t > 0 with t² = p: if a·p ≤ L ≤ b·p, then √a/√L ≤ 1/t ≤ √b/√L.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Pairs.lean#L156-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/PairsToBound/Pairs.lean#L156-L173

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

theorem PairsToBound.inv_between_sqrt {a b L t p : ℝ} (ha : 0 < a) (ht : 0 < t) (htp : t ^ 2 = p) (h1 : a * p ≤ L) (h2 : L ≤ b * p) :
    Real.sqrt a / Real.sqrt L ≤ 1 / t ∧ 1 / t ≤ Real.sqrt b / Real.sqrt L := by sorry
