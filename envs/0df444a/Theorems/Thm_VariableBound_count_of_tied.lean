-- Prove2me | Theorems.Thm_VariableBound_count_of_tied
-- name    : VariableBound.count_of_tied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:43:12.595196+00:00
-- url     : https://prove2.me/theorems/95611200-173b-4313-b12d-d44d8d97d154
-- title:
--   Variable Bound: count of tied
-- statement:
--   A machine that runs A on every input and counts within the three bounds is a machine that counts
--   within the three bounds. This statement names no function.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/Tied.lean#L63-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/Tied.lean#L63-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_TiedDefs
import Definitions.Def_UniformInK_Top_End
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_VariableBound_Printed_Tied
set_option autoImplicit false
section
section
open VariableBound
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End UniformInK UniformInK.End VariableBound.Decide

theorem VariableBound.count_of_tied {A : List Bool × U → List Bool} {e : List Bool → ℕ} {rn rm : ℕ → ℝ} (h : TiedOut A e id rn rm) : SatM.CountUniformInRate rn rm := by sorry
