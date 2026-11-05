-- Prove2me | Theorems.Thm_UniformInK_stNodeStepU
-- name    : UniformInK.stNodeStepU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:09:10.544098+00:00
-- url     : https://prove2.me/theorems/9a76456c-e58e-4c59-a929-13eb5be8c418
-- title:
--   Uniform In K: st Node Step U
-- statement:
--   Both children of a node are nodes: one more step, and τ more units at the heavy child.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L259-L259
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L259-L259

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK

theorem UniformInK.stNodeStepU : StNodeStepU := by sorry
