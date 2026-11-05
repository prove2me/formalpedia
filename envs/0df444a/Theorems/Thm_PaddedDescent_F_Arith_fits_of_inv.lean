-- Prove2me | Theorems.Thm_PaddedDescent_F_Arith_fits_of_inv
-- name    : PaddedDescent.F.Arith.fits_of_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:02.295307+00:00
-- url     : https://prove2.me/theorems/9cd55c8d-caa3-4f8a-9126-9eebc745218f
-- title:
--   Arith: fits of inv
-- statement:
--   If the invariant holds at level j ≤ t, then a pad of length F ≥ 2^e suffices for the work list
--   at level j and for all the steps below it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithFits.lean#L27-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/ArithFits.lean#L27-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithInv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_PaddedDescent_F_ArithFits
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)

theorem PaddedDescent.F.Arith.fits_of_inv {t X Z Qm Wm L Lw e F : ℕ} (hZ : 25 * Kseq t ^ 2 ≤ 2 * Z) (hZQ : Z ≤ Qm) (hL : Qm + 1 ≤ 2 ^ L)
    (hLw : Kseq t * (3 * Wm + 14) + 4 * Qm + 10 ≤ 2 ^ Lw)
    (he1 : 4 * (X + Z) ≤ e) (he2 : L * Kseq t ^ 2 ≤ e) (he3 : Kseq t ≤ e)
    (he4 : L * (2 * Kseq t ^ 2) + (X + Z) + Lw + 1 ≤ e) (hF : 2 ^ e ≤ F) :
    ∀ j, j ≤ t → ∀ lam B cnt, Inv t X Z Qm Wm L j lam B cnt → Fits F (Kseq j) lam B cnt (schedL j) := by sorry
