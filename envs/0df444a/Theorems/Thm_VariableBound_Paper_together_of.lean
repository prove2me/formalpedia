-- Prove2me | Theorems.Thm_VariableBound_Paper_together_of
-- name    : VariableBound.Paper.together_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:14:55.487938+00:00
-- url     : https://prove2.me/theorems/1b5d78ad-7400-464c-9865-9c46226d48f2
-- title:
--   Paper: together of
-- statement:
--   Every proof of `SatM.TargetUniform` gives one machine and one constant for Theorem 1, Theorem D (b)
--   and Corollary 11 in the paper's wording.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Forms.lean#L67-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Forms.lean#L67-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInKStatement
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Forms
set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms Turing
open Sat3 (CNF)

theorem VariableBound.Paper.together_of (h : SatM.TargetUniform) : TogetherAllOccur := by sorry
