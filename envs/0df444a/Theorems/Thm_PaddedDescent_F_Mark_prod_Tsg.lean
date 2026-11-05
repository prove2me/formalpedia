-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_prod_Tsg
-- name    : PaddedDescent.F.Mark.prod_Tsg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:13.0175+00:00
-- url     : https://prove2.me/theorems/dfb10299-ddb4-45b3-b8ec-8f5caa3e7f4c
-- title:
--   Mark: prod Tsg
-- statement:
--   For good layers and every assignment, the product of the signed sums is 1 if the assignment
--   satisfies all layers and 0 otherwise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L60-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L60-L76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkSums
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog

theorem PaddedDescent.F.Mark.prod_Tsg {n w : ℕ} (σ : Fin n → Bool) : ∀ {Ls : List Fml}, Good n w Ls →
    (Ls.map fun L => Tsg w (nvio (ext σ) L)).prod = if ∀ L ∈ Ls, nvio (ext σ) L = 0 then 1 else 0
  := by sorry
