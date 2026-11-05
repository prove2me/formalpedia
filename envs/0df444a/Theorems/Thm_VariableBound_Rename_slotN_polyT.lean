-- Prove2me | Theorems.Thm_VariableBound_Rename_slotN_polyT
-- name    : VariableBound.Rename.slotN_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:15:53.562277+00:00
-- url     : https://prove2.me/theorems/126757e5-58e7-4f46-a3b9-5c3206a39d0a
-- title:
--   Rename: slot N poly T
-- statement:
--   The number of a slot is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Cert.lean#L42-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Cert.lean#L42-L44

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

theorem VariableBound.Rename.slotN_polyT {o : α → Option (ℕ × Bool)} (ho : PolyT o) : PolyT fun x => slotN (o x) := by sorry
