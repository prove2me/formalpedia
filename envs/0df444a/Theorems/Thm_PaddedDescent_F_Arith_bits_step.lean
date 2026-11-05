-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_bits_step
-- name    : PaddedDescent.F.Arith.bits_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:44.6991+00:00
-- url     : https://prove2.me/theorems/5b21996f-755f-4842-a975-f586ee555f4b
-- title:
--   Arith: bits step
-- statement:
--   The arithmetic of `Inv.step`, line `bits`, with plain variables (K3 = K³, G6 = (g·g)³, G3 = g³,
--   q = g⁴Λ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L78-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithInv.lean#L78-L85

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

theorem PaddedDescent.F.Arith.bits_step {B B' K3 G6 G3 q Qm Wm : ℕ} (O2 : B' ≤ 6 * (G3 * B) + 8 * q) (O8a : 6 * G3 * K3 ≤ G6)
    (O8b : 24 * K3 ≤ 16 * G6) (hq : q ≤ Qm) (h3 : B * G6 + 16 * Qm * G6 ≤ Wm) :
    B' * K3 + 16 * Qm * K3 ≤ Wm := by sorry
