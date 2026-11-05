-- Prove2me | Theorems.Thm_PaddedDescent_F_Price_min_price_nat
-- name    : PaddedDescent.F.Price.min_price_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:07:53.634595+00:00
-- url     : https://prove2.me/theorems/f4e82190-e33f-4bad-8f67-115703079d73
-- title:
--   Price: min price nat
-- statement:
--   The cheaper price plus the g²(g−1)n bits of the straight edges is at most the natural number
--   `Ubar g n`, by `min_price_le` and ρ < 717/800.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Price.lean#L40-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/Price.lean#L40-L54

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

theorem PaddedDescent.F.Price.min_price_nat (g n y : ℕ) : g ^ 2 * (g - 1) * n + min (priceRow g n y) (priceCol g n y) ≤ Ubar g n := by sorry
