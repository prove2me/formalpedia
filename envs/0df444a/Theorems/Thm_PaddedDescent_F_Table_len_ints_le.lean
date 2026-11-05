-- Prove2me | Theorems.Thm_PaddedDescent_F_Table_len_ints_le
-- name    : PaddedDescent.F.Table.len_ints_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:48:54.395461+00:00
-- url     : https://prove2.me/theorems/196d30a0-37ec-4e4d-bd3c-13d32d7d9c67
-- title:
--   Table: len ints le
-- statement:
--   The Table construction uses the len ints le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Table.lean#L158-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Table.lean#L158-L165

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_StepMachines_Prog_SideBasics
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_PaddedDescent_F_Table
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Table
open Groundwork Groundwork.Prog Finset

theorem PaddedDescent.F.Table.len_ints_le {B : ℕ} : ∀ (r : List ℤ), (∀ z ∈ r, z.natAbs ≤ 2 ^ B) → len r ≤ r.length * (3 * B + 10) + 2
  := by sorry
