-- Prove2me | Theorems.Thm_VariableBound_Search_argminD_polyT
-- name    : VariableBound.Search.argminD_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:42:33.987618+00:00
-- url     : https://prove2.me/theorems/f5f2a1ca-3a2a-42d7-a0de-bd978a5b7f83
-- title:
--   Search: argmin D poly T
-- statement:
--   The first member with the smallest key is polynomial-time, if the key and the list are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L77-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L77-L94

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

theorem VariableBound.Search.argminD_polyT {key : α → List ℕ → ℤ} {fam : α → List (List ℕ)} (hk : PolyT fun p : α × List ℕ => key p.1 p.2) (hf : PolyT fam) :
    PolyT fun x => argminD (key x) (fam x) := by sorry
