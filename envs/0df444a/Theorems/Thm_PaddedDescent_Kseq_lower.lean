-- Prove2me | Theorems.Thm_PaddedDescent_Kseq_lower
-- name    : PaddedDescent.Kseq_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:16.051039+00:00
-- url     : https://prove2.me/theorems/d02bab2c-a290-485f-870a-e95b2ea80e4d
-- title:
--   Padded Descent: Kseq lower
-- statement:
--   Lower bound: 256·4^j ≤ K_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Seq.lean#L65-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Seq.lean#L65-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
set_option autoImplicit false
section
section
open PaddedDescent

theorem PaddedDescent.Kseq_lower (j : ℕ) : 256 * 4 ^ j ≤ Kseq j := by sorry
