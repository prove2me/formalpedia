-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_card_links_at_le
-- name    : PaddedDescent.F.Mark.Size.card_links_at_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:11.079856+00:00
-- url     : https://prove2.me/theorems/aa87e991-cb81-449c-8d69-74298609ee05
-- title:
--   Size: card links at le
-- statement:
--   At a node a, a clause has at most two links, and none if it does not touch a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L195-L219
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L195-L219

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter


set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}

theorem PaddedDescent.F.Mark.Size.card_links_at_le {a : ℕ} (ha : a < g) (e : ℕ) :
    #(((range g).erase a).filter fun b => linkB g n Ls e (min a b) (max a b) = true) ≤ if tchB g n Ls a e = true then 2 else 0 := by sorry
