-- Prove2me | Theorems.Thm_PaddedDescent_F_Mark_Tsg_of_le
-- name    : PaddedDescent.F.Mark.Tsg_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:05.551916+00:00
-- url     : https://prove2.me/theorems/e472d20f-a662-4721-aed4-52576f8885dd
-- title:
--   Mark: Tsg of le
-- statement:
--   The signed sum cut off at w is exact for v ≤ w: it is 1 if v = 0 and 0 otherwise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L32-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/MarkSums.lean#L32-L39

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

theorem PaddedDescent.F.Mark.Tsg_of_le {w v : ℕ} (h : v ≤ w) : Tsg w v = if v = 0 then 1 else 0 := by sorry
