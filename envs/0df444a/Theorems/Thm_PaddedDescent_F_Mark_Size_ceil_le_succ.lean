-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Size_ceil_le_succ
-- name    : PaddedDescent.F.Mark.Size.ceil_le_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:31:49.462764+00:00
-- url     : https://prove2.me/theorems/2f40e43e-a193-4af1-b37e-3155317c5953
-- title:
--   Size: ceil le succ
-- statement:
--   A string of t bits has at most t / b + 1 blocks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L410-L414
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSize.lean#L410-L414

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

theorem PaddedDescent.F.Mark.Size.ceil_le_succ (b t : ℕ) : (t + b - 1) / b ≤ t / b + 1 := by sorry
