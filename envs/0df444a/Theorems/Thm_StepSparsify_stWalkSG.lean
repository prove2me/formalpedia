-- Prove2me | Theorems.Thm_StepSparsify_stWalkSG
-- name    : StepSparsify.stWalkSG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:06:25.523793+00:00
-- url     : https://prove2.me/theorems/269fa2ec-4179-4404-b178-b653a5090501
-- title:
--   Step Sparsify: st Walk SG
-- statement:
--   If the procedure has stopped at every node that is listed when the paths are cut after d steps,
--   the pad has at least 2·(number of these nodes) − 1 units and the word of every state of the walk
--   fits under the pad, then `walkSG` returns the sum of the
--   values of these nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/Walk.lean#L30-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/StepSparsify/Walk.lean#L30-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_CountKSatRate_Walk
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_PaddedDescent_F_Top
import Definitions.Def_StepSparsify_Walk
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open StepSparsify
open Groundwork Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F CountKSatRate UniformInK

theorem StepSparsify.stWalkSG : StWalkSG := by sorry
