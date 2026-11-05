-- Prove2me | Theorems.Thm_WidthK_Refine_not_heart_of_none
-- name    : WidthK.Refine.not_heart_of_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:07:25.388475+00:00
-- url     : https://prove2.me/theorems/d54594b0-0174-4cd5-9e88-030a7cb83929
-- title:
--   Refine: not heart of none
-- statement:
--   The same for a set H of any size: H is not a heart for size j if `tryP` has no answer at (j, |H|).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L283-L287
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/sparsification/SparsifyWidthK/Refine.lean#L283-L287

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

theorem WidthK.Refine.not_heart_of_none {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {j : ℕ} {H : Finset PLit} (hθ : ∀ r, 1 ≤ r → 1 ≤ θ r) (hs : NF s)
    (hj : j ≤ k) (h : (j, H.card) ∈ pairsK k → tryP θ k s (j, H.card) = none) : ¬ Heart θ (toFin s) j H := by sorry
