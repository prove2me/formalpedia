-- Prove2me | Theorems.Thm_WidthK_Refine_mem_pairsK
-- name    : WidthK.Refine.mem_pairsK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:39:56.471692+00:00
-- url     : https://prove2.me/theorems/7ec77e8a-6011-4f80-ab93-436f0c32605c
-- title:
--   Refine: mem pairs K
-- statement:
--   The pairs that are tried: 1 ≤ h < j ≤ k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L165-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L165-L173

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_StepMachines_Math_SparsifyProg
import Definitions.Def_StepMachines_Math_SparsifyProg
import Mathlib.Data.List.Nodup
import Definitions.Def_SparsifyWidthK_Refine
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open WidthK WidthK.Refine
open Finset Groundwork Groundwork.Sparsify WidthK.Prog

theorem WidthK.Refine.mem_pairsK {k : ℕ} {jh : ℕ × ℕ} : jh ∈ pairsK k ↔ 0 < jh.2 ∧ jh.2 < jh.1 ∧ jh.1 ≤ k := by sorry
