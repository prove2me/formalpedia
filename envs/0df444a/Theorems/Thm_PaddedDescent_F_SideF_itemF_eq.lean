-- Prove2me | Theorems.Thm_PaddedDescent_F_SideF_itemF_eq
-- name    : PaddedDescent.F.SideF.itemF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:59.786961+00:00
-- url     : https://prove2.me/theorems/95a1f898-b216-465c-b0ec-3fb2541eb476
-- title:
--   Side F: item F eq
-- statement:
--   `itemF` is `sideItem`, if the pad has at least 2^n units.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/SideF.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/SideF.lean#L35-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_F_Price
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_SideF
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.SideF
open Groundwork Groundwork.Prog Groundwork.Grid Finset

theorem PaddedDescent.F.SideF.itemF_eq {pad : U} (g : ℕ) (tr : Bool) {n : ℕ} (y a b : ℕ) (z θ : List Bool) (i i' : ℕ)
    (h : 2 ^ n ≤ pad.length) : itemF pad g tr n y a b z θ i i' = sideItem g tr n y a b z θ i i' := by sorry
