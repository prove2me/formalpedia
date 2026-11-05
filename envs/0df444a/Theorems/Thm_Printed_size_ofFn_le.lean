-- Prove2me | Theorems.Thm_Printed_size_ofFn_le
-- name    : Printed.size_ofFn_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:49:40.067204+00:00
-- url     : https://prove2.me/theorems/7bd379ce-3dff-4d70-b315-226957f315cf
-- title:
--   Printed: size of Fn le
-- statement:
--   The size of a list of K strings of at most λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L162-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L162-L171

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
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {K lam : ℕ}

theorem Printed.size_ofFn_le (θ : Fin K → List Bool) (h : ∀ u, (θ u).length ≤ lam) : size (List.ofFn θ) ≤ K * (2 * lam + 2) + 1 := by sorry
