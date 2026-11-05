-- Prove2me | Theorems.Thm_WidthK_Refine_leaf_of_pickK
-- name    : WidthK.Refine.leaf_of_pickK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:31:04.443856+00:00
-- url     : https://prove2.me/theorems/98e36cf7-aa22-411a-b4ca-7c5b44cc6e06
-- title:
--   Refine: leaf of pick K
-- statement:
--   Where `pickK` has no answer, no clause size up to k has a heart.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L304-L306
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L304-L306

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

theorem WidthK.Refine.leaf_of_pickK {θ : ℕ → ℕ} {k : ℕ} {s : PFml} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (hs : NF s)
    (h : pickK θ k s = none) : Leaf θ k (toFin s) := by sorry
