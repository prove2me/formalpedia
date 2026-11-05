-- Prove2me | Theorems.Thm_WidthK_Refine_mem_heartsP
-- name    : WidthK.Refine.mem_heartsP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:07:21.467338+00:00
-- url     : https://prove2.me/theorems/e598771d-527d-4bc2-b099-183ef6425cbb
-- title:
--   Refine: mem hearts P
-- statement:
--   The candidate hearts are exactly the sublists of length h of the clauses of length j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L152-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L152-L160

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.Refine.mem_heartsP {k : ℕ} {s : PFml} {j h : ℕ} {H : PCl} (hj : j ≤ k) :
    H ∈ heartsP k s j h ↔ ∃ C ∈ s, C.length = j ∧ H.Sublist C ∧ H.length = h := by sorry
