-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_exponents_le
-- name    : PaddedDescent.F.Arith.exponents_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:07.797947+00:00
-- url     : https://prove2.me/theorems/d1ec38d3-083c-4ad0-b815-3797830ca940
-- title:
--   Arith: exponents le
-- statement:
--   One inequality that dominates the exponents of all budgets.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L253-L260
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L253-L260

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

theorem PaddedDescent.F.Arith.exponents_le {s n : ℕ} (hY : Ytop s ^ 6 ≤ n) :
    4 * (Xof s n + Zof s) + (Lof s n * (2 * Kseq (depthOf s) ^ 2) + (Xof s n + Zof s) + 2 * Lof s n + 1) + Kseq (depthOf s)
      ≤ 8 * Xof s n := by sorry
