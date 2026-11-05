-- Prove2me | Theorems.Thm_PaddedDescent_size_le_sqrt
-- name    : PaddedDescent.size_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:40:14.335653+00:00
-- url     : https://prove2.me/theorems/d640f2b9-3eac-4fe3-aeb5-a406662ecc17
-- title:
--   Padded Descent: size le sqrt
-- statement:
--   The number of binary digits of n is at most 2·⌊√n⌋ + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L30-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Threshold.lean#L30-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_Threshold
set_option autoImplicit false
section
section
open PaddedDescent

theorem PaddedDescent.size_le_sqrt (n : ℕ) : Nat.size n ≤ 2 * Nat.sqrt n + 2 := by sorry
