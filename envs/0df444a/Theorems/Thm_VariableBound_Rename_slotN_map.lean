-- Prove2me | Theorems.Thm_VariableBound_Rename_slotN_map
-- name    : VariableBound.Rename.slotN_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:14:14.710369+00:00
-- url     : https://prove2.me/theorems/f69d81bb-f680-44c4-b53a-b78b21e3bd19
-- title:
--   Rename: slot N map
-- statement:
--   The number of a slot, with natural numbers as variables, is that of `Sat3.slot`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Code.lean#L25-L26
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Rename/Code.lean#L25-L26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_VariableBound_Paper_Rename_Code
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open VariableBound VariableBound.Rename
open Groundwork Groundwork.Prog Groundwork.Decode PaddedDescent.F ClauseBound.Alg MainTheoremForms
open Sat3 (CNF)

theorem VariableBound.Rename.slotN_map {n : ℕ} (o : Option (Sat3.Lit n)) : slotN (o.map fun l => (l.1.val, l.2)) = Sat3.slot o := by sorry
