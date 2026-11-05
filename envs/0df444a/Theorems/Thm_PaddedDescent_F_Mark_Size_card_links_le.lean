-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_card_links_le
-- name    : PaddedDescent.F.Mark.Size.card_links_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:17.547311+00:00
-- url     : https://prove2.me/theorems/225d72bf-d3d1-46b6-9fea-b58ab270d42b
-- title:
--   Size: card links le
-- statement:
--   A clause of k literals has at most k − 1 links, and an empty clause has none.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L145-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L145-L153

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}

theorem PaddedDescent.F.Mark.Size.card_links_le (e : ℕ) :
    #(((range g) ×ˢ (range g)).filter fun p => linkB g n Ls e p.1 p.2 = true) ≤ (clAt Ls e).2.length - 1 := by sorry
