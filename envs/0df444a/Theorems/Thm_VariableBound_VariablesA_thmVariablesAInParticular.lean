-- Prove2me | Theorems.Thm_VariableBound_VariablesA_thmVariablesAInParticular
-- name    : VariableBound.VariablesA.thmVariablesAInParticular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:12:10.538458+00:00
-- url     : https://prove2.me/theorems/bf72d859-7d7b-4bea-b7d7-e73f0a944ce0
-- title:
--   Variables A: thm Variables AIn Particular
-- statement:
--   Theorem D (a), last sentence: if e_ℓ ≤ c·(log K_ℓ)^(−α′) for all ℓ, with α′ > 0, then a machine
--   with the bound of Theorem D (a) takes at most 2^{C'·k²·n·log log n/(log n)^α′} steps, for n ≥ K₀^17
--   and 3 ≤ k ≤ (log n)^(1/4).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/StepSparsify.lean#L143-L189
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/StepSparsify.lean#L143-L189

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

theorem VariableBound.VariablesA.thmVariablesAInParticular : ThmVariablesAInParticular := by sorry
