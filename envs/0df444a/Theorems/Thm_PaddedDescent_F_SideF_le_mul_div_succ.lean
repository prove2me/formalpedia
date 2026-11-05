-- Prove2me | Theorems.Thm_PaddedDescent_F_SideF_le_mul_div_succ
-- name    : PaddedDescent.F.SideF.le_mul_div_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:16:15.487704+00:00
-- url     : https://prove2.me/theorems/36ed7bfb-fd54-4411-a01d-ca2654851f7d
-- title:
--   Side F: le mul div succ
-- statement:
--   x ≤ y·(x / y + 1) for y > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/SideF.lean#L91-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/SideF.lean#L91-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_F_Price
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_SideF
set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.SideF
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.SideF.le_mul_div_succ (x : ℕ) {y : ℕ} (hy : 0 < y) : x ≤ y * (x / y + 1) := by sorry
