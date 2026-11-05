-- Prove2me | Theorems.Thm_VariableBound_Paper_corMinIsMainTheorem
-- name    : VariableBound.Paper.corMinIsMainTheorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:26:54.981046+00:00
-- url     : https://prove2.me/theorems/990f576a-6465-4d5f-9eaa-cd5fd1e0d4e4
-- title:
--   Paper: cor Min Is Main Theorem
-- statement:
--   After Corollary 11: «This is the Main Theorem.» For every machine and every constant the bound
--   of Corollary 11 and the bound of Theorem 1 are the same.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Forms.lean#L48-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/Forms.lean#L48-L51

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

theorem VariableBound.Paper.corMinIsMainTheorem : CorMinIsMainTheoremStmt := by sorry
