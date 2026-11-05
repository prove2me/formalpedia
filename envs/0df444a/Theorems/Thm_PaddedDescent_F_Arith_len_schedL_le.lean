-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_len_schedL_le
-- name    : PaddedDescent.F.Arith.len_schedL_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:15.118626+00:00
-- url     : https://prove2.me/theorems/399e275c-5ad0-405a-82f5-94037893c0b3
-- title:
--   Arith: len sched L le
-- statement:
--   The word of the schedule of depth j has length at most j·(8·K_j + 8) + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L48-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L48-L58

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithCol
import Definitions.Def_PaddedDescent_F_ArithSched
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork PaddedDescent.F.Lists
open PaddedDescent.F.Arith

theorem PaddedDescent.F.Arith.len_schedL_le (j : ℕ) : len (schedL j) ≤ j * (8 * Kseq j + 8) + 2 := by sorry
