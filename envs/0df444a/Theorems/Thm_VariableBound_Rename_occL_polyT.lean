-- Prove2me | Theorems.Thm_VariableBound_Rename_occL_polyT
-- name    : VariableBound.Rename.occL_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:36.454566+00:00
-- url     : https://prove2.me/theorems/86919a6c-bf8b-4bd3-baa6-3a7237eeec17
-- title:
--   Rename: occ L poly T
-- statement:
--   The list of the variables that occur is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Cert.lean#L25-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Cert.lean#L25-L27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Paper_Rename_Cert
set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg
variable {α : Type} [Enc α]

theorem VariableBound.Rename.occL_polyT {ψ : α → Fml} (hψ : PolyT ψ) : PolyT fun x => occL (ψ x) := by sorry
