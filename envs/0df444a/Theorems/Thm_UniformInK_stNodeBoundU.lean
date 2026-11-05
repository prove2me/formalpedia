-- Prove2me | Theorems.Thm_UniformInK_stNodeBoundU
-- name    : UniformInK.stNodeBoundU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:42:20.908128+00:00
-- url     : https://prove2.me/theorems/6b571f71-2d06-4c04-926b-bd4f362a5cff
-- title:
--   Uniform In K: st Node Bound U
-- statement:
--   `Bound.bound`, in the form of the interface.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Bound.lean#L106-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/UniformInK/Spars/Bound.lean#L106-L106

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Definitions.Def_UniformInK_Spars_Bound
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK

theorem UniformInK.stNodeBoundU : StNodeBoundU := by sorry
