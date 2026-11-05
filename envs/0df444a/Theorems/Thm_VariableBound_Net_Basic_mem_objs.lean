-- Prove2me | Theorems.Thm_VariableBound_Net_Basic_mem_objs
-- name    : VariableBound.Net.Basic.mem_objs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:40:45.274474+00:00
-- url     : https://prove2.me/theorems/37b9ca69-6cc0-4315-97fb-21b17531de54
-- title:
--   Basic: mem objs
-- statement:
--   The objects are the triples (0, e, 0) with e < m and the triples (1, e, j) with j < r and e ∈
--   Λ_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L32-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Net/Basic.lean#L32-L42

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

theorem VariableBound.Net.Basic.mem_objs {x : ℕ × ℕ × ℕ} : x ∈ objs D ↔
    (x.1 = 0 ∧ x.2.1 < D.1.length ∧ x.2.2 = 0) ∨ (x.1 = 1 ∧ x.2.2 < D.2.length ∧ x.2.1 ∈ D.2.getD x.2.2 []) := by sorry
