-- Prove2me | Theorems.Thm_VariableBound_Paper_numSatOcc_lt
-- name    : VariableBound.Paper.numSatOcc_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:37:33.913211+00:00
-- url     : https://prove2.me/theorems/249ad03f-f302-41e5-ab89-3159ae9ef993
-- title:
--   Paper: num Sat Occ lt
-- statement:
--   The number of satisfying assignments, as assignments of the n variables that occur, is below
--   2^(n+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/MainTheorem.lean#L42-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Paper/MainTheorem.lean#L42-L47

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

theorem VariableBound.Paper.numSatOcc_lt {N : ℕ} (φ : CNF N) : numSatOcc φ < 2 ^ (numOcc φ + 1) := by sorry
