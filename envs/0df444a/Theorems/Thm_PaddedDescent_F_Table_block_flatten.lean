-- Prove2me | Theorems.Thm_PaddedDescent_F_Table_block_flatten
-- name    : PaddedDescent.F.Table.block_flatten
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:13:08.397322+00:00
-- url     : https://prove2.me/theorems/59ff0a19-6bbb-43e6-ae9a-1c740eb4907b
-- title:
--   Table: block flatten
-- statement:
--   The j-th block of a concatenation of words of length ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Table.lean#L36-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Table.lean#L36-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_PaddedDescent_F_Table
import Theorems.Thm_Groundwork_Decode_block_flatten
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Table
open Groundwork Groundwork.Prog Finset

theorem PaddedDescent.F.Table.block_flatten {ℓ : ℕ} : ∀ (L : List (List Bool)) (j : ℕ), (∀ w ∈ L, w.length = ℓ) → j < L.length →
    block ℓ j L.flatten = L.getD j []
  := by sorry
