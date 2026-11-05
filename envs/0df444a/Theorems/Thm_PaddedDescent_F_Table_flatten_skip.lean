-- Prove2me | Theorems.Thm_PaddedDescent_F_Table_flatten_skip
-- name    : PaddedDescent.F.Table.flatten_skip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:48:39.390191+00:00
-- url     : https://prove2.me/theorems/7a94e1a0-0f9e-42ea-a656-1eef173694fd
-- title:
--   Table: flatten skip
-- statement:
--   An empty word may be left out of a concatenation.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Table.lean#L54-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Table.lean#L54-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_PaddedDescent_F_Table
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Table
open Groundwork Groundwork.Prog Finset

theorem PaddedDescent.F.Table.flatten_skip (t : ℕ → List Bool) : ∀ (K v : ℕ), v < K → t v = [] →
    ((List.range K).map t).flatten = ((List.range (K - 1)).map fun j => t (skip v j)).flatten
  := by sorry
