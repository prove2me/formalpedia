-- Prove2me | Theorems.Thm_SparsifyThenCount_stRoundsDG
-- name    : SparsifyThenCount.stRoundsDG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:42:32.905615+00:00
-- url     : https://prove2.me/theorems/fde32dd5-a378-404d-8c60-9e63629354a9
-- title:
--   Sparsify Then Count: st Rounds DG
-- statement:
--   A number F ≥ 2^(`VariableBound.restD` k K n s) is at least 2·2^(⌊n/2^s⌋+1) − 1, which suffices
--   for the rounds of the walk: ⌊n/2^s⌋ + 2 is one of the four summands of `restD`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/Correct.lean#L38-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/SparsifyThenCount/Correct.lean#L38-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyThenCount_Defs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_UniformInK_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Definitions.Def_VariableBound_Top_Correct
import Definitions.Def_SparsifyThenCount_Correct
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open SparsifyThenCount
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK UniformInK.Correct VariableBound VariableBound.Correct VariableBound.Net
open PaddedDescent.F.Mark (WfL occ nSat)

theorem SparsifyThenCount.stRoundsDG : StRoundsDG := by sorry
