-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_gseq_add_two_mul_lt
-- name    : PaddedDescent.F.Arith.gseq_add_two_mul_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:03.828324+00:00
-- url     : https://prove2.me/theorems/6c814e06-8404-4f88-bb54-83604c0fbb04
-- title:
--   Arith: gseq add two mul lt
-- statement:
--   (g_j + 2)·K_j < 2^(2^(9+j)).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithCol.lean#L33-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithCol.lean#L33-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithCol
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent

theorem PaddedDescent.F.Arith.gseq_add_two_mul_lt (j : ℕ) : (gseq j + 2) * Kseq j < 2 ^ 2 ^ (9 + j) := by sorry
