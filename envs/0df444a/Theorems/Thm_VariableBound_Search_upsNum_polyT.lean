-- Prove2me | Theorems.Thm_VariableBound_Search_upsNum_polyT
-- name    : VariableBound.Search.upsNum_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:17:31.66937+00:00
-- url     : https://prove2.me/theorems/9fa0adc5-4d32-4383-aae2-bc1107a3c16e
-- title:
--   Search: ups Num poly T
-- statement:
--   The numerator of Υ is polynomial-time, for m, n̄, β, r̄, t̄ in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L44-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L44-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Search_Correct
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Search_Cert
set_option autoImplicit false
section
section
open VariableBound VariableBound.Search
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]

theorem VariableBound.Search.upsNum_polyT {m nb β rb tb : α → ℕ} {v : α → ℤ} {L : α → List (List ℕ)} (hm : Unary m) (hnb : Unary nb) (hβ : Unary β) (hrb : Unary rb)
    (htb : Unary tb) (hv : PolyT v) (hL : PolyT L) : PolyT fun x => upsNum (m x) (nb x) (β x) (rb x) (tb x) (v x) (L x) := by sorry
