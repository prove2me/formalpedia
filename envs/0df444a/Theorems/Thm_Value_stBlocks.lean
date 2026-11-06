-- Prove2me | Theorems.Thm_Value_stBlocks
-- name    : Value.stBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:23:39.480243+00:00
-- url     : https://prove2.me/theorems/18134665-3825-489a-b458-c4a3c009f2bb
-- title:
--   Value: st Blocks
-- statement:
--   The choices of one string of L bits per edge {γ, γ'} with all appended bits 0 are the choices of
--   «one string θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair {a,b} of nodes in different groups».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L174-L185
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Value/Blocks.lean#L174-L185

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Words
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_Value_Blocks
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
variable {C : Type} [HasSize C] {g K : ℕ}
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

theorem Value.stBlocks : StBlocks := by sorry
