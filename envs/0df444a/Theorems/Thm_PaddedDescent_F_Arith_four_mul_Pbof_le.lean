-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_four_mul_Pbof_le
-- name    : PaddedDescent.F.Arith.four_mul_Pbof_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:17:39.353499+00:00
-- url     : https://prove2.me/theorems/a927397e-d2a9-4672-92df-d6ed83b4f48a
-- title:
--   Arith: four mul Pbof le
-- statement:
--   4·g·Pb ≤ K_t·X, for g = `gtop s`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L274-L302
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithTopInv.lean#L274-L302

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

theorem PaddedDescent.F.Arith.four_mul_Pbof_le {Δ s n : ℕ} (hΔ : Δ ≤ 2 ^ betaOf s) (hY : Ytop s ^ 6 ≤ n) : 4 * (gtop s * Pbof Δ s n) ≤ Ktop s * Xof s n := by sorry
