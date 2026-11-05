-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_linkB_iff
-- name    : PaddedDescent.F.Mark.Size.linkB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:51:59.959574+00:00
-- url     : https://prove2.me/theorems/a77781f8-2704-4445-bebf-efe796abd8a3
-- title:
--   Size: link B iff
-- statement:
--   a and b are neighbours in the chain of clause e exactly when a < b, e touches both, and e
--   touches no node between them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L37-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L37-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_PaddedDescent_F_MarkSize
import Theorems.Thm_Groundwork_Prog_Count_linkB_iff

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Size
open Groundwork Groundwork.Prog Finset
variable {g n : ℕ} {Ls : List Fml}

theorem PaddedDescent.F.Mark.Size.linkB_iff {e a b : ℕ} : linkB g n Ls e a b = true ↔
    a < b ∧ tchB g n Ls a e = true ∧ tchB g n Ls b e = true ∧ ∀ c < g, a < c → c < b → tchB g n Ls c e = false := by sorry
