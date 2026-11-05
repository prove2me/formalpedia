-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_trunc_nil_cons
-- name    : PaddedDescent.F.Mark.trunc_nil_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:31.741332+00:00
-- url     : https://prove2.me/theorems/c83f9f0a-7c5b-4603-92d0-c34000ea4843
-- title:
--   Mark: trunc nil cons
-- statement:
--   With an empty first layer, one evaluation on good layers is the number of assignments that
--   satisfy all layers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L92-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L92-L95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkSums
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog

theorem PaddedDescent.F.Mark.trunc_nil_cons {n w : ℕ} {Ls : List Fml} (h : Good n w Ls) :
    trunc n w ([] :: Ls) = ((univ.filter fun σ : Fin n → Bool => ∀ L ∈ Ls, nvio (ext σ) L = 0).card : ℤ) := by sorry
