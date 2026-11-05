-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_inc_mem
-- name    : VariableBound.Net.Basic.inc_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:18:45.438999+00:00
-- url     : https://prove2.me/theorems/e5d996df-9d7c-46ee-9901-e9516285046f
-- title:
--   Basic: inc mem
-- statement:
--   An incidence (E, j) has j < r and E ∈ Λ_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L66-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L66-L70

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

theorem VariableBound.Net.Basic.inc_mem {o : ℕ} (h : o < (objs D).length) (h1 : (obAt D o).1 = 1) :
    (obAt D o).2.2 < D.2.length ∧ (obAt D o).2.1 ∈ D.2.getD (obAt D o).2.2 [] := by sorry
