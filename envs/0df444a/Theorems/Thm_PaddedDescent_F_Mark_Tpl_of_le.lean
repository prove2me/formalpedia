-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Tpl_of_le
-- name    : PaddedDescent.F.Mark.Tpl_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:09.348938+00:00
-- url     : https://prove2.me/theorems/76a453c7-a9a3-4c3d-a93c-839ccecc5887
-- title:
--   Mark: Tpl of le
-- statement:
--   The unsigned sum cut off at w is exact for v ≤ w: it is 2^v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L42-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L42-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_PaddedDescent_F_MarkSums
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark
open Finset Groundwork.Prog

theorem PaddedDescent.F.Mark.Tpl_of_le {w v : ℕ} (h : v ≤ w) : Tpl w v = 2 ^ v := by sorry
