-- Prove2me | Theorems.Thm_VariableBound_VariablesA_stepSparsifySmall
-- name    : VariableBound.VariablesA.stepSparsifySmall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:43.00427+00:00
-- url     : https://prove2.me/theorems/408a210a-c3f2-4e3b-8b98-1cf35f10cdd8
-- title:
--   Variables A: step Sparsify Small
-- statement:
--   Step 5: «For the finitely many smaller n …, trying all assignments is within the bound»: n ≤
--   c·k²·e·n·log(k/e) and k·log n ≤ c·k²·e·n·log(k/e) for 2 ≤ n < n₁, k ≥ 3 and (log n)^(−C₀) ≤ e ≤ 1,
--   with c depending on C₀ and n₁ only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/StepSparsify.lean#L107-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/StepSparsify.lean#L107-L138

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Printed_VariablesA_StepSparsify
set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork Turing PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End MainTheoremForms
open Sat3 (CNF)

theorem VariableBound.VariablesA.stepSparsifySmall : StepSparsifySmallStmt := by sorry
