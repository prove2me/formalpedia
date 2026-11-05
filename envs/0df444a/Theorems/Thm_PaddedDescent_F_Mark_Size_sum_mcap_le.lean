-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_sum_mcap_le
-- name    : PaddedDescent.F.Mark.Size.sum_mcap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:20.173039+00:00
-- url     : https://prove2.me/theorems/f0d8fcec-8a13-45b6-b850-38dd52c45f69
-- title:
--   Size: sum mcap le
-- statement:
--   The capacities at a node a sum to at most 2(2 + β) bits for each clause that touches a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L320-L327
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L320-L327

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

theorem PaddedDescent.F.Mark.Size.sum_mcap_le {k w y β b : ℕ} (h0 : 0 < b) (h : adm k g n w Ls y = true) {a : ℕ} (ha : a < g) :
    ∑ a' ∈ (range g).erase a, mcap g n β b Ls y a a' ≤ 2 * (2 + β) * (tch g n Ls a).length := by sorry
