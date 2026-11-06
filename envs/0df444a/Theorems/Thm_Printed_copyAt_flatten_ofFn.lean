-- Prove2me | Theorems.Thm_Printed_copyAt_flatten_ofFn
-- name    : Printed.copyAt_flatten_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:48:35.765528+00:00
-- url     : https://prove2.me/theorems/b25cf69d-245c-42e6-ba73-da1ca6cff58e
-- title:
--   Printed: copy At flatten of Fn
-- statement:
--   The copy at u of the concatenation is the string number u.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L80-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Printed/Coding.lean#L80-L96

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

theorem Printed.copyAt_flatten_ofFn (w : Fin K) (θ : Fin K → List Bool) (h : ∀ u, u ≠ w → (θ u).length = lam) (hw : θ w = []) (u : Fin K) (hu : u ≠ w) :
    copyAt lam w u (List.ofFn θ).flatten = θ u := by sorry
