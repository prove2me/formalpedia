-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_adm_iff
-- name    : PaddedDescent.F.Mark.Size.adm_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:43:44.42323+00:00
-- url     : https://prove2.me/theorems/90d74635-7bc2-427f-8142-80f8b1fe0972
-- title:
--   Size: adm iff
-- statement:
--   `adm` is true exactly when, in every layer, the four conditions below hold.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L278-L298
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L278-L298

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}

theorem PaddedDescent.F.Mark.Size.adm_iff {k w y : ℕ} : adm k g n w Ls y = true ↔ ∀ i < Ls.length,
    ((List.range g).map fun a => mu g Ls y a a i).sum ≤ w ∧
    ((List.range g).map fun a => ((List.range a).map fun a' => mu g Ls y a' a i).sum).sum ≤ (k - 1) * w ∧
    ∀ a < g, ∀ a' < g, (a' < a → Groundwork.Prog.digit (cls Ls).length y ((a * g + a') * Ls.length + i) = 0) ∧
      (a < a' → mu g Ls y a a' i ≤ (tst g n Ls a a' i).length) := by sorry
