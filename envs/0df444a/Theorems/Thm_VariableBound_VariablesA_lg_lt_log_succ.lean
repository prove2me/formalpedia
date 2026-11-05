-- Prove2me | Theorems.Thm_VariableBound_VariablesA_lg_lt_log_succ
-- name    : VariableBound.VariablesA.lg_lt_log_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:18.053409+00:00
-- url     : https://prove2.me/theorems/d48e815d-891e-4a98-9b28-bd14508bdca5
-- title:
--   Variables A: lg lt log succ
-- statement:
--   log₂ n < ⌊log₂ n⌋ + 1, for n ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Arith.lean#L38-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Arith.lean#L38-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_ClauseBound_TopN_End
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End MainTheoremForms
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)

theorem VariableBound.VariablesA.lg_lt_log_succ {n : ℕ} (hn : 1 ≤ n) : MainTheoremForms.lg n < (Nat.log 2 n : ℝ) + 1 := by sorry
