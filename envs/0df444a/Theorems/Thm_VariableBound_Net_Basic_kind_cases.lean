-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_kind_cases
-- name    : VariableBound.Net.Basic.kind_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:59:18.808883+00:00
-- url     : https://prove2.me/theorems/c2cdfc55-e4bc-4eb4-bbaf-5487ea2601b1
-- title:
--   Basic: kind cases
-- statement:
--   An object (at a place o below the number of objects) is of kind 0 or of kind 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L62-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L62-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Basic
open Groundwork Groundwork.Prog PaddedDescent.F
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Basic.kind_cases {o : ℕ} (h : o < (objs D).length) : (obAt D o).1 = 0 ∨ (obAt D o).1 = 1 := by sorry
