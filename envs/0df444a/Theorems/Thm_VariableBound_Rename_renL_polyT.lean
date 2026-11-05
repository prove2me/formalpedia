-- Prove2me | Theorems.Thm_VariableBound_Rename_renL_polyT
-- name    : VariableBound.Rename.renL_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:16:26.615129+00:00
-- url     : https://prove2.me/theorems/a9d159f8-d3f9-49e7-8402-a5e7f7fe85d7
-- title:
--   Rename: ren L poly T
-- statement:
--   Replacing every variable by its position in a list is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Cert.lean#L30-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Cert.lean#L30-L32

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

theorem VariableBound.Rename.renL_polyT {L : α → List ℕ} {ψ : α → Fml} (hL : PolyT L) (hψ : PolyT ψ) : PolyT fun x => renL (L x) (ψ x) := by sorry
