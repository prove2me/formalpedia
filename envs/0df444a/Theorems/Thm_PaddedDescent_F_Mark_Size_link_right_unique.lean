-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_link_right_unique
-- name    : PaddedDescent.F.Mark.Size.link_right_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:33.389601+00:00
-- url     : https://prove2.me/theorems/2ebb0a43-8098-4ca7-a64f-0dfebc902308
-- title:
--   Size: link right unique
-- statement:
--   The lower end of a link determines its upper end.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L66-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L66-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}

theorem PaddedDescent.F.Mark.Size.link_right_unique {e a b b' : ℕ} (hb : b < g) (hb' : b' < g) (h : linkB g n Ls e a b = true) (h' : linkB g n Ls e a b' = true) : b = b' := by sorry
