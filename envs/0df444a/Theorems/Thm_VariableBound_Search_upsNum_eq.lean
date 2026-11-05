-- Prove2me | Theorems.Thm_VariableBound_Search_upsNum_eq
-- name    : VariableBound.Search.upsNum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:41:19.002707+00:00
-- url     : https://prove2.me/theorems/af98e1dd-50ae-4212-b7ac-bec79af35d3b
-- title:
--   Search: ups Num eq
-- statement:
--   `upsNum` with the powers taken in the natural numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L36-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L36-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Search_Cert
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]

theorem VariableBound.Search.upsNum_eq (m nb β rb tb : ℕ) (x : ℤ) (L : List (List ℕ)) :
    upsNum m nb β rb tb x L = ((4 ^ L.length * 2 ^ tb * (15 * nb) ^ (rb - L.length) : ℕ) : ℤ) * x +
      ((3 ^ L.length * 2 ^ (β - 1) * (15 * nb + 16) ^ (rb - L.length) * loadSum m L : ℕ) : ℤ) := by sorry
