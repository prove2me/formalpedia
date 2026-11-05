-- Prove2me | Theorems.Thm_VariableBound_Search_loadSum_polyT
-- name    : VariableBound.Search.loadSum_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:17:28.5302+00:00
-- url     : https://prove2.me/theorems/e46eea84-3bfd-4380-aee3-2a2701bee260
-- title:
--   Search: load Sum poly T
-- statement:
--   Σ_E 2^load(E) is polynomial-time, for m in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L31-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Search/Cert.lean#L31-L33

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

theorem VariableBound.Search.loadSum_polyT {m : α → ℕ} {L : α → List (List ℕ)} (hm : Unary m) (hL : PolyT L) : PolyT fun x => loadSum (m x) (L x) := by sorry
