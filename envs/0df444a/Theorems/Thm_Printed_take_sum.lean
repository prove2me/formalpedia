-- Prove2me | Theorems.Thm_Printed_take_sum
-- name    : Printed.take_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:51:06.443206+00:00
-- url     : https://prove2.me/theorems/b74ec880-e78c-4ecc-8ffe-c0ed5745ec4f
-- title:
--   Printed: take sum
-- statement:
--   The number of bits of the first i strings.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L70-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L70-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_Eight_SecNetworks_Clique
import Definitions.Def_Value_Clique
import Mathlib.Tactic
import Definitions.Def_Printed_Coding
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {K lam : ℕ}

theorem Printed.take_sum (w : Fin K) (θ : Fin K → List Bool) (h : ∀ u, u ≠ w → (θ u).length = lam) (hw : θ w = []) (i : ℕ) (hi : i ≤ K) :
    (((List.ofFn θ).map List.length).take i).sum = (if w.val < i then i - 1 else i) * lam := by sorry
