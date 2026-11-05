-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_schedState_succ
-- name    : PaddedDescent.F.Arith.schedState_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:47.702196+00:00
-- url     : https://prove2.me/theorems/53f65f7d-f753-40f5-b744-c5da13aa19f7
-- title:
--   Arith: sched State succ
-- statement:
--   One round of `schedF` without its cut-off takes the state after j rounds to the state after j +
--   1 rounds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L42-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L42-L45

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

theorem PaddedDescent.F.Arith.schedState_succ (j : ℕ) :
    (((schedState j).2.1, mulU (schedState j).2.1 (schedState j).2.2) :: (schedState j).1,
      sqU (mulU (schedState j).2.1 (schedState j).2.2), (schedState j).2.2 ++ (schedState j).2.2) = schedState (j + 1) := by sorry
