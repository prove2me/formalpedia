-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_prof_exponent_le
-- name    : PaddedDescent.F.Arith.prof_exponent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:23.525371+00:00
-- url     : https://prove2.me/theorems/f1bd410e-13c6-420e-83c1-9609fa6372be
-- title:
--   Arith: prof exponent le
-- statement:
--   The logarithm of the number of profiles is at most ⌊n/2^s⌋, for s = sOf n ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithMark.lean#L38-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithMark.lean#L38-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithStack
import Definitions.Def_PaddedDescent_F_ArithMark
set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent

theorem PaddedDescent.F.Arith.prof_exponent_le {n : ℕ} (hs : 1 ≤ sOf n) :
    (betaOf (sOf n) + Nat.size n) * (Ytop (sOf n) * (layersOf (sOf n) + 2)) ≤ n / 2 ^ sOf n := by sorry
