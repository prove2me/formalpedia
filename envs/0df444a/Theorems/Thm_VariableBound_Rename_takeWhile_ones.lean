-- Prove2me | Theorems.Thm_VariableBound_Rename_takeWhile_ones
-- name    : VariableBound.Rename.takeWhile_ones
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:08:35.572593+00:00
-- url     : https://prove2.me/theorems/dda7b087-8254-494b-b705-682d46f1ead1
-- title:
--   Rename: take While ones
-- statement:
--   The leading 1s of 1ᵃ 0 v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Compact.lean#L50-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Compact.lean#L50-L51

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
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_takeWhile
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.takeWhile


set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Groundwork.DecodeK (clauseDec decK decK_enc)
open Sat3 (CNF)

theorem VariableBound.Rename.takeWhile_ones (a : ℕ) (v : List Bool) : ((List.replicate a true ++ false :: v).takeWhile id).length = a := by sorry
