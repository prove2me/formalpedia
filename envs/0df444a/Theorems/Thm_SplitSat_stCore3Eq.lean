-- Prove2me | Theorems.Thm_SplitSat_stCore3Eq
-- name    : SplitSat.stCore3Eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:44:21.283297+00:00
-- url     : https://prove2.me/theorems/d3fea6c9-3742-44b5-8c3a-561b0aa160e8
-- title:
--   Split Sat: st Core3 Eq
-- statement:
--   The machine of Theorem 2 is the reader of the input followed by `core3`: the statement
--   `SplitSat.StCore3Eq`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Procedure.lean#L38-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Procedure.lean#L38-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_WidthK_Top_Poly
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_Eight_ViaGrouping_Alg
import Mathlib.Tactic
import Definitions.Def_SplitSat_Procedure
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight Eight.ViaGrouping GraphProblems

theorem SplitSat.stCore3Eq : StCore3Eq := by sorry
