-- Prove2me | Theorems.Thm_Suffices_main_bound
-- name    : Suffices.main_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:26:18.417873+00:00
-- url     : https://prove2.me/theorems/fb152e49-9780-4571-b43f-1b2879f043aa
-- title:
--   Suffices: main bound
-- statement:
--   For c = c₁ + A·(14M + 2)^A + 2A + c₂ + 22: the bound on the states of the loop plus that on the
--   states of the machine for sparse formulas, and 20·N², are each at most c·N^c (used in
--   `stSufficesOf`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L104-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Suffices/Sizes.lean#L104-L116

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Defs
import Definitions.Def_Exits_Tested
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Mathlib.Tactic.Ring
import Definitions.Def_Suffices_Sizes
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog CountKSat Exits

theorem Suffices.main_bound {c c₁ c₂ A M N : ℕ} (hc : c = c₁ + A * (14 * M + 2) ^ A + 2 * A + c₂ + 22) (hN : 1 ≤ N) :
    c₁ * N ^ c₁ + A * ((14 * M + 2) * N ^ 2) ^ A ≤ c * N ^ c ∧ 20 * N ^ 2 ≤ c * N ^ c := by sorry
