-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_mcap_le
-- name    : PaddedDescent.F.Mark.Size.mcap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:24.943979+00:00
-- url     : https://prove2.me/theorems/843ccec7-b674-4700-81a4-a78f0b86cb5f
-- title:
--   Size: mcap le
-- statement:
--   The capacity of a pair is at most (2 + β) bits for each bit of its strings.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L309-L317
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L309-L317

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}

theorem PaddedDescent.F.Mark.Size.mcap_le {k w y β b : ℕ} (h0 : 0 < b) (h : adm k g n w Ls y = true) {a a' : ℕ} (ha : a < g) (ha' : a' < g) (hne : a ≠ a') :
    mcap g n β b Ls y a a' ≤ (2 + β) * ∑ i ∈ range Ls.length, (tst g n Ls a a' i).length := by sorry
