-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_stackLen_le
-- name    : PaddedDescent.F.Arith.stackLen_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:08.417052+00:00
-- url     : https://prove2.me/theorems/523c8f72-1933-40ac-bb5e-3d4493cff45f
-- title:
--   Arith: stack Len le
-- statement:
--   The last part of `StAW`: the stack of the walk for width k fits under the pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L134-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L134-L144

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_PaddedDescent_F_ArithStack
set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)

theorem PaddedDescent.F.Arith.stackLen_le {k n C₀ F : ℕ} (hk : 1 ≤ k) (hs : s0K k ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F) :
    stackLen k (tauOf (sOf n)) n (inLen k n) ≤ F := by sorry
