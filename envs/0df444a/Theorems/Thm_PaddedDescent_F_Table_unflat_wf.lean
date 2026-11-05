-- Prove2me | Theorems.Thm_PaddedDescent_F_Table_unflat_wf
-- name    : PaddedDescent.F.Table.unflat_wf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:48:47.825961+00:00
-- url     : https://prove2.me/theorems/14433722-44b0-4041-a262-251adc8a6e34
-- title:
--   Table: unflat wf
-- statement:
--   `unflat` of a word of the right length is a well-formed query.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Table.lean#L128-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Table.lean#L128-L140

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

theorem PaddedDescent.F.Table.unflat_wf {K ℓ : ℕ} (v : Fin K) {w : List Bool} (hw : w.length = (K - 1) * ℓ) :
    ∃ θ : Fin K → List Bool, unflat K ℓ v.1 w = List.ofFn θ ∧ WFQ ℓ v θ := by sorry
