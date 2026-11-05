-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_schedLen_le
-- name    : PaddedDescent.F.Arith.schedLen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:24.464205+00:00
-- url     : https://prove2.me/theorems/14ab02d3-76a5-41cc-841c-d8f9d5b4ab29
-- title:
--   Arith: sched Len le
-- statement:
--   The second part of `StA`: the computation of the schedule fits under the pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L113-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithSched.lean#L113-L141

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
open Arith
open PaddedDescent.F.Arith

theorem PaddedDescent.F.Arith.schedLen_le {n C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) :
    schedLen (depthOf (sOf n)) ≤ F := by sorry
