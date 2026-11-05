-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_le_pad_of_le_pow
-- name    : PaddedDescent.F.Arith.le_pad_of_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:32:32.564235+00:00
-- url     : https://prove2.me/theorems/7bdf82c8-faab-4886-8bb4-da46c203c990
-- title:
--   Arith: le pad of le pow
-- statement:
--   Whatever is at most (2^size n)^e with e ≤ Y = Ytop (sOf n), for instance n^e, is below the pad.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L58-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithStack.lean#L58-L61

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

theorem PaddedDescent.F.Arith.le_pad_of_le_pow {n e W C₀ F : ℕ} (hs : 1 ≤ sOf n) (hC : 1 ≤ C₀) (hF : 2 ^ (C₀ * (n / 2 ^ sOf n + 1)) ≤ F)
    (he : e ≤ Ytop (sOf n)) (hW : W ≤ 2 ^ (e * Nat.size n)) : W ≤ F := by sorry
