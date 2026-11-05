-- Prove2me | Theorems.Thm_PaddedDescent_F_Price_U_side_le
-- name    : PaddedDescent.F.Price.U_side_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:07:31.450006+00:00
-- url     : https://prove2.me/theorems/d5065918-27e3-4e0b-8cc2-f6db8a86580a
-- title:
--   Price: U side le
-- statement:
--   The side that `sideCtx` chooses has U ≤ Ubar.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Price.lean#L57-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Price.lean#L57-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_Price
set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent PaddedDescent.F PaddedDescent.F.Price
open Groundwork Groundwork.Prog Groundwork.Grid

theorem PaddedDescent.F.Price.U_side_le (g n : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) (y : ℕ) :
    (sideN g (decide (priceCol g n y < priceRow g n y)) n Rm y).U ≤ Ubar g n := by sorry
