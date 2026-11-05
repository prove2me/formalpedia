-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_len_schedState_le
-- name    : PaddedDescent.F.Arith.len_schedState_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:13.459897+00:00
-- url     : https://prove2.me/theorems/eae9504e-3cd7-4d08-be7f-e8ade8bd3d8d
-- title:
--   Arith: len sched State le
-- statement:
--   The word of the state after j rounds has length at most `schedLen j`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L61-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L61-L64

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

theorem PaddedDescent.F.Arith.len_schedState_le (j : ℕ) : len (schedState j) ≤ schedLen j := by sorry
