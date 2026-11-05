-- Prove2me | Theorems.Thm_WidthK_Refine_pickK_none
-- name    : WidthK.Refine.pickK_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:30:46.650407+00:00
-- url     : https://prove2.me/theorems/6662937b-c241-4480-ab32-f7a3a734f4aa
-- title:
--   Refine: pick K none
-- statement:
--   Where `pickK` has no answer, `tryP` has none at any pair.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L234-L235
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L234-L235

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

theorem WidthK.Refine.pickK_none {θ : ℕ → ℕ} {k : ℕ} {s : PFml} (h : pickK θ k s = none) : ∀ x ∈ pairsK k, tryP θ k s x = none := by sorry
