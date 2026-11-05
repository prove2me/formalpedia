-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_tchB_iff
-- name    : VariableBound.Net.Basic.tchB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:46:13.878877+00:00
-- url     : https://prove2.me/theorems/76fd630e-44de-4e4c-9259-0410050a77d5
-- title:
--   Basic: tch B iff
-- statement:
--   An object touches the nodes that hold the variables of its clause; an incidence (E, j) also
--   touches h(j).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L147-L149
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L147-L149

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card
import Definitions.Def_VariableBound_Net_Basic
set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.Basic
open Groundwork Groundwork.Prog PaddedDescent.F
open PaddedDescent.F.Mark (Cl qv vio WfL occ)
variable {k g n : ℕ} {D : Dat}

theorem VariableBound.Net.Basic.tchB_iff {a o : ℕ} : tchB g n D a o = true ↔
    (∃ l ∈ clOf D o, l.1 / qv g n = a) ∨ ((obAt D o).1 = 1 ∧ home g (obAt D o).2.2 = a) := by sorry
