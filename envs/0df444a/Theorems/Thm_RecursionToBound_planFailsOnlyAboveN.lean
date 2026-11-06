-- Prove2me | Theorems.Thm_RecursionToBound_planFailsOnlyAboveN
-- name    : RecursionToBound.planFailsOnlyAboveN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:00:20.145795+00:00
-- url     : https://prove2.me/theorems/895af345-34ff-46a4-9ca6-490150bb3b14
-- title:
--   Recursion To Bound: plan Fails Only Above N
-- statement:
--   For n ≥ n₁ the function sparsifies unless the exponent exceeds n; and where there is a plan, it
--   is the sum of the exponent for the outputs and the exponent for the walk.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L92-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/RecursionToBound/Guard.lean#L92-L115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Cert_Numbers
import Definitions.Def_ToTuring_Poly_NetFun
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Definitions.Def_RecursionToBound_Guard
set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.TopN VariableBound.Net
variable {Idx : Type} [Enc Idx] {S : Solver Idx}

theorem RecursionToBound.planFailsOnlyAboveN : PlanFailsOnlyAboveN := by sorry
