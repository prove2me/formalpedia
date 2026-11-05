-- Prove2me | Theorems.Thm_VariableBound_Rename_encN_polyT
-- name    : VariableBound.Rename.encN_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:39:27.097583+00:00
-- url     : https://prove2.me/theorems/7d1f9ea8-78ee-4b01-8daf-aa804a057319
-- title:
--   Rename: enc N poly T
-- statement:
--   Writing (k, n, ψ) as a bit string is polynomial-time, with k and n in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Cert.lean#L47-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Cert.lean#L47-L58

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

theorem VariableBound.Rename.encN_polyT {ku : α → U} {d : α → U × Fml} (hk : PolyT ku) (hd : PolyT d) : PolyT fun x => encN (ku x) (d x) := by sorry
