-- Prove2me | Theorems.Thm_PaddedDescent_F_Table_len_rows_le
-- name    : PaddedDescent.F.Table.len_rows_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:49:11.21119+00:00
-- url     : https://prove2.me/theorems/a75fea72-e9ad-43d0-a014-2084fac09630
-- title:
--   Table: len rows le
-- statement:
--   The Table construction uses the len rows le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Table.lean#L167-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Table.lean#L167-L173

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

theorem PaddedDescent.F.Table.len_rows_le {X : ℕ} : ∀ (T : List (List ℤ)), (∀ r ∈ T, len r ≤ X + 2) → len T ≤ T.length * (X + 4) + 2
  := by sorry
