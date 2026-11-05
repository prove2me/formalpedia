-- Prove2me | Theorems.Thm_Printed_length_flatten_ofFn
-- name    : Printed.length_flatten_ofFn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:50:28.220364+00:00
-- url     : https://prove2.me/theorems/06e31e68-cb9a-4af7-b782-3bb1bf478795
-- title:
--   Printed: length flatten of Fn
-- statement:
--   The concatenation has (K − 1)λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L75-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L75-L77

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

theorem Printed.length_flatten_ofFn (w : Fin K) (θ : Fin K → List Bool) (h : ∀ u, u ≠ w → (θ u).length = lam) (hw : θ w = []) :
    (List.ofFn θ).flatten.length = (K - 1) * lam := by sorry
