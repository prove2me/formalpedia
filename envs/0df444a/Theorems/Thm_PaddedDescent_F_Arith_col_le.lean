-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_col_le
-- name    : PaddedDescent.F.Arith.col_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:52.960199+00:00
-- url     : https://prove2.me/theorems/65d15d5f-1e21-4da5-a009-44724a3afb6e
-- title:
--   Arith: col le
-- statement:
--   The groupings of the g nodes into K groups, functions [g] → [K] as in the proof of Lemma 1: K^g
--   ≤ 2^(K_t).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L195-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L195-L198

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
variable {t X Z Qm Wm L j lam B cnt : ℕ}

theorem PaddedDescent.F.Arith.col_le (hj : j + 1 ≤ t) : Kseq j ^ gseq j ≤ 2 ^ Kseq t := by sorry
