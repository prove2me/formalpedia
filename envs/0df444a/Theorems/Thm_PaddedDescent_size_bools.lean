-- Prove2me | Theorems.Thm_PaddedDescent_size_bools
-- name    : PaddedDescent.size_bools
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:53:07.371428+00:00
-- url     : https://prove2.me/theorems/11b7ca85-85d6-4d5a-aeb5-4399fd5a1993
-- title:
--   Padded Descent: size bools
-- statement:
--   The Padded Descent construction uses the size bools property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Pad.lean#L54-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Pad.lean#L54-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_PaddedDescent_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_PaddedDescent_Pad
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}

theorem PaddedDescent.size_bools (x : List Bool) : size x = 2 * x.length + 1 := by sorry
