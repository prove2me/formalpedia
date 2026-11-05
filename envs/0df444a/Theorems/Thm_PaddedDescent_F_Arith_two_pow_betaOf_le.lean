-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_two_pow_betaOf_le
-- name    : PaddedDescent.F.Arith.two_pow_betaOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:44:34.044432+00:00
-- url     : https://prove2.me/theorems/97b65608-1451-49b0-9195-4d1e9e1ed507
-- title:
--   Arith: two pow beta Of le
-- statement:
--   2^(4β + 10s + 1000) ≤ n for s = sOf n ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L68-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L68-L71

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

theorem PaddedDescent.F.Arith.two_pow_betaOf_le {n : ℕ} (hs : 1 ≤ sOf n) : 2 ^ (4 * betaOf (sOf n) + 10 * sOf n + 1000) ≤ n := by sorry
