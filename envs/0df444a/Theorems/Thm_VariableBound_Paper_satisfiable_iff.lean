-- Prove2me | Theorems.Thm_VariableBound_Paper_satisfiable_iff
-- name    : VariableBound.Paper.satisfiable_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:37:57.067025+00:00
-- url     : https://prove2.me/theorems/dc034b29-e977-47cf-ba9b-d00f3bd4824d
-- title:
--   Paper: satisfiable iff
-- statement:
--   A formula is satisfiable if and only if its number of satisfying assignments, as assignments of
--   the variables that occur, is not 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/MainTheorem.lean#L34-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/MainTheorem.lean#L34-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_VariableBound_Paper_Rename_Time
import Definitions.Def_ClauseBound_MainBoth
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_VariableBound_Paper_MainTheorem
set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open Groundwork Turing CountKSatRate VariableBound.Rename MainTheoremForms
open Sat3 (CNF)

theorem VariableBound.Paper.satisfiable_iff {N : ℕ} (φ : CNF N) : Sat3.Satisfiable φ ↔ numSatOcc φ ≠ 0 := by sorry
