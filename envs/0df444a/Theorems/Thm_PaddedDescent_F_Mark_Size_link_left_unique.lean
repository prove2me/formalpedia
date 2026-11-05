-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_link_left_unique
-- name    : PaddedDescent.F.Mark.Size.link_left_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:43:00.884795+00:00
-- url     : https://prove2.me/theorems/383ad052-5217-4aad-9cac-930c96948640
-- title:
--   Size: link left unique
-- statement:
--   The upper end of a link determines its lower end.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L57-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L57-L63

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

theorem PaddedDescent.F.Mark.Size.link_left_unique {e a a' b : ℕ} (hb : b ≤ g) (h : linkB g n Ls e a b = true) (h' : linkB g n Ls e a' b = true) : a = a' := by sorry
