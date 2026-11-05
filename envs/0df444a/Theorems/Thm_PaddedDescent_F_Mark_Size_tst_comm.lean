-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_tst_comm
-- name    : PaddedDescent.F.Mark.Size.tst_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:43:41.804795+00:00
-- url     : https://prove2.me/theorems/6c5208b0-ad7d-4fcd-abc3-17d2d0aa15f7
-- title:
--   Size: tst comm
-- statement:
--   The clauses whose marks two nodes compare do not depend on the order of the nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L272-L272
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L272-L272

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

theorem PaddedDescent.F.Mark.Size.tst_comm (a b i : ℕ) : tst g n Ls a b i = tst g n Ls b a i := by sorry
