-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_card_links_lt
-- name    : PaddedDescent.F.Mark.Size.card_links_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:48.452387+00:00
-- url     : https://prove2.me/theorems/ff990166-0a08-4df0-8d89-c441a3ccb8cd
-- title:
--   Size: card links lt
-- statement:
--   A clause that touches a node has fewer links than touched nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L85-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L85-L112

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

theorem PaddedDescent.F.Mark.Size.card_links_lt (e : ℕ) (h : ∃ a < g, tchB g n Ls a e = true) :
    #(((range g) ×ˢ (range g)).filter fun p => linkB g n Ls e p.1 p.2 = true) < #((range g).filter fun a => tchB g n Ls a e = true) := by sorry
