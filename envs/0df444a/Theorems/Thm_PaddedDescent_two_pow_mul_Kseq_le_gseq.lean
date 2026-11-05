-- Prove2me | Theorems.Thm_PaddedDescent_two_pow_mul_Kseq_le_gseq
-- name    : PaddedDescent.two_pow_mul_Kseq_le_gseq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:05.228576+00:00
-- url     : https://prove2.me/theorems/c569a23c-8890-45d4-a84b-bb213f03342a
-- title:
--   Padded Descent: two pow mul Kseq le gseq
-- statement:
--   2^47·K_j ≤ g_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Seq.lean#L86-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/Seq.lean#L86-L88

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

theorem PaddedDescent.two_pow_mul_Kseq_le_gseq (j : ℕ) : 2 ^ 47 * Kseq j ≤ gseq j := by sorry
