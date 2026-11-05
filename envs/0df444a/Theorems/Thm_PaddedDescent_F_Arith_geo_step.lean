-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_geo_step
-- name    : PaddedDescent.F.Arith.geo_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:20.817749+00:00
-- url     : https://prove2.me/theorems/6c13b29f-cb2a-4dff-ac8b-c5990f0e21d3
-- title:
--   Arith: geo step
-- statement:
--   The arithmetic of `Inv.step`, line `geo`, with plain variables (a = 8963^j, b = 10000^j, q' =
--   K²Λ', q = g⁴Λ, G = g⁴).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L70-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L70-L74

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

theorem PaddedDescent.F.Arith.geo_step {a b q' q G X Z : ℕ} (O1 : 10000 * q' ≤ 8963 * q + 10000 * G) (hG : 10000 * G ≤ 1037 * Z)
    (h1 : a * 8963 * q ≤ b * 10000 * X + a * 8963 * Z) : a * q' ≤ b * X + a * Z := by sorry
