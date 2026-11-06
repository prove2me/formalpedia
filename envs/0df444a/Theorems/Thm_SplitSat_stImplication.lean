-- Prove2me | Theorems.Thm_SplitSat_stImplication
-- name    : SplitSat.stImplication
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:04:38.464945+00:00
-- url     : https://prove2.me/theorems/d73d8aee-676d-43ca-bc4e-292296062d51
-- title:
--   Split Sat: st Implication
-- statement:
--   **«s_3 = 0 implies s_k = 0 for every k ≥ 3», for machines cut into steps**: for every family Ds
--   of procedures for 3-SAT, one for each exponent δ₃ > 0, and for every k ≥ 3 and δ > 0, the reduction
--   run on one member of that family has polynomial-time steps and decides k-SAT with the exponent δ.
--   This is the statement `SplitSat.StImplication`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L75-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SplitSat/Main.lean#L75-L78

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Reader
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_SplitSat_Main
set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping
open scoped NNReal ENNReal

theorem SplitSat.stImplication : StImplication := by sorry
