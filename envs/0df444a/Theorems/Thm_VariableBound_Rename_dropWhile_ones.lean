-- Prove2me | Theorems.Thm_VariableBound_Rename_dropWhile_ones
-- name    : VariableBound.Rename.dropWhile_ones
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:08:58.140593+00:00
-- url     : https://prove2.me/theorems/509928cc-e8c5-4fca-9dc9-6f95498033cd
-- title:
--   Rename: drop While ones
-- statement:
--   What follows 1ᵃ 0 in 1ᵃ 0 v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Compact.lean#L54-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Compact.lean#L54-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Theorems.Thm_Groundwork_DecodeK_decK_enc
import Theorems.Thm_Groundwork_PolyT_dropWhile
attribute [local fun_prop] Groundwork.PolyT.dropWhile


set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Groundwork.DecodeK (clauseDec decK decK_enc)
open Sat3 (CNF)

theorem VariableBound.Rename.dropWhile_ones (a : ℕ) (v : List Bool) : ((List.replicate a true ++ false :: v).dropWhile id).tail = v := by sorry
