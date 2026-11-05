-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_Kseq_mono
-- name    : PaddedDescent.F.Arith.Kseq_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:17:58.161459+00:00
-- url     : https://prove2.me/theorems/b5583edd-7baf-4771-822d-dd769b64ec5b
-- title:
--   Arith: Kseq mono
-- statement:
--   K_i ≤ K_j for i ≤ j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L50-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L50-L50

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

theorem PaddedDescent.F.Arith.Kseq_mono {i j : ℕ} (h : i ≤ j) : Kseq i ≤ Kseq j := by sorry
