-- Prove2me | Theorems.Thm_VariableBound_Paper_thmVariablesBFor_of
-- name    : VariableBound.Paper.thmVariablesBFor_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:14:37.796618+00:00
-- url     : https://prove2.me/theorems/2ee02fe9-1066-4d3f-944d-5d1a732945b7
-- title:
--   Paper: thm Variables BFor of
-- statement:
--   From the bound in n of `UniformInKStatement.lean` with the constant C to the bound of Theorem D (b)
--   with the constant 3C, for the same machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Forms.lean#L55-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Forms.lean#L55-L56

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

theorem VariableBound.Paper.thmVariablesBFor_of {M : TM2ComputableAux Bool Bool} {C : ℕ} (h : SatM.CountsTMN M (SatM.boundNK (SatK.rN 1 (1 / 2)) C)) : ThmVariablesBFor M (3 * C) := by sorry
