-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_top_rounds
-- name    : PaddedDescent.F.Arith.top_rounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:21.183433+00:00
-- url     : https://prove2.me/theorems/edac1e84-e62c-417e-a691-40839045ec32
-- title:
--   Arith: top rounds
-- statement:
--   Conjunct 3 of StAW: the rounds of the walk.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L382-L389
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L382-L389

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {k Δ s n F : ℕ}

theorem PaddedDescent.F.Arith.top_rounds (hs : s0K k ≤ s) (hF : 2 ^ (8 * Xof s n) ≤ F) :
    2 * (∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j) ≤ F + 1 := by sorry
