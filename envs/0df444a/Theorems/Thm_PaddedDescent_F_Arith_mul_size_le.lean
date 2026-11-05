-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_mul_size_le
-- name    : PaddedDescent.F.Arith.mul_size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:33.625015+00:00
-- url     : https://prove2.me/theorems/8f8bea07-f0cd-4d71-89de-0d2baf86cc3e
-- title:
--   Arith: mul size le
-- statement:
--   e·size n ≤ n/2^(sOf n) for every e ≤ Y = Ytop (sOf n), when sOf n ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L51-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L51-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_PaddedDescent_Threshold
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_PaddedDescent_F_ArithStack
import Theorems.Thm_Groundwork_SatNet_mul_size_le

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork Groundwork.Sparsify PaddedDescent.F.Lists
open WidthK (theta bsum)
open WidthK.Prog (stepK)

theorem PaddedDescent.F.Arith.mul_size_le {n e : ℕ} (hs : 1 ≤ sOf n) (he : e ≤ Ytop (sOf n)) : e * Nat.size n ≤ n / 2 ^ sOf n := by sorry
