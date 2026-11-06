-- Prove2me | Theorems.Thm_UniformInK_stNodeRootU
-- name    : UniformInK.stNodeRootU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:09:10.423988+00:00
-- url     : https://prove2.me/theorems/904df9e7-a37c-40fc-a119-6be8010a0f44
-- title:
--   Uniform In K: st Node Root U
-- statement:
--   The root of the tree is a node with both counters 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L256-L256
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Step.lean#L256-L256

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

theorem UniformInK.stNodeRootU : StNodeRootU := by sorry
