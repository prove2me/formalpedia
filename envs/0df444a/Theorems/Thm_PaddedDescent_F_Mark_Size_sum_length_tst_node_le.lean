-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_sum_length_tst_node_le
-- name    : PaddedDescent.F.Mark.Size.sum_length_tst_node_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:51.310306+00:00
-- url     : https://prove2.me/theorems/82d246ee-b3b3-4bb0-abb0-2fb9c6c41336
-- title:
--   Size: sum length tst node le
-- statement:
--   All the strings that a node a shares with the other nodes together have at most twice as many
--   bits as clauses touch a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L223-L247
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L223-L247

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

theorem PaddedDescent.F.Mark.Size.sum_length_tst_node_le {a : ℕ} (ha : a < g) :
    ∑ b ∈ (range g).erase a, ∑ i ∈ range Ls.length, (tst g n Ls a b i).length ≤ 2 * (tch g n Ls a).length := by sorry
