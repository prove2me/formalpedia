-- Prove2me | Theorems.Thm_VariableBound_stPlanLeD
-- name    : VariableBound.stPlanLeD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:05:47.409281+00:00
-- url     : https://prove2.me/theorems/8a149bb7-948f-48e3-a39a-06778bb2dec9
-- title:
--   Variable Bound: st Plan Le D
-- statement:
--   The exponent of a plan, or else n, is at most n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithPlan.lean#L27-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Top/ArithPlan.lean#L27-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Mathlib.Tactic.SplitIfs
import Definitions.Def_VariableBound_Top_ArithPlan
set_option autoImplicit false
section
section
open VariableBound
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.Net

theorem VariableBound.stPlanLeD : StPlanLeD := by sorry
