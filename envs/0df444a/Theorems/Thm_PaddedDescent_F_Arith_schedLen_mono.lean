-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_schedLen_mono
-- name    : PaddedDescent.F.Arith.schedLen_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:13.811414+00:00
-- url     : https://prove2.me/theorems/80269e7e-b57c-41a5-acc9-e2d419f2da86
-- title:
--   Arith: sched Len mono
-- statement:
--   `schedLen` grows with the depth.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L67-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L67-L71

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

theorem PaddedDescent.F.Arith.schedLen_mono {i j : ℕ} (h : i ≤ j) : schedLen i ≤ schedLen j := by sorry
