-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_sum_choose_le_two_pow
-- name    : PaddedDescent.F.Arith.sum_choose_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:03:41.306916+00:00
-- url     : https://prove2.me/theorems/51627cb4-0441-4e72-9b19-1ad8a14476b1
-- title:
--   Arith: sum choose le two pow
-- statement:
--   The bound of the sparsification lemma for the number of leaves, for width k and s ≥ s0K k, is at
--   most 2^(⌊n/2^s⌋+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithWalk.lean#L26-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithWalk.lean#L26-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_PaddedDescent_F_ArithWalk
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith

theorem PaddedDescent.F.Arith.sum_choose_le_two_pow {k s : ℕ} (hs : s0K k ≤ s) (n : ℕ) :
    ∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j ≤ 2 ^ (n / 2 ^ s + 1) := by sorry
