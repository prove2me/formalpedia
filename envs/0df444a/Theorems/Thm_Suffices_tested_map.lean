-- Prove2me | Theorems.Thm_Suffices_tested_map
-- name    : Suffices.tested_map
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:26:33.353645+00:00
-- url     : https://prove2.me/theorems/f1725838-de60-4a26-9ddc-09a18cdd637b
-- title:
--   Suffices: tested map
-- statement:
--   The entries of a mapped list that are tested are the images of the entries tested by the
--   composed test.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L31-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L31-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Defs
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Tactic.Ring
import Definitions.Def_Suffices_Sizes
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits

theorem Suffices.tested_map {μ ν : Type} (f : μ → ν) (u : ν → Bool) (l : List μ) : tested u (l.map f) = (tested (fun x => u (f x)) l).map f := by sorry
