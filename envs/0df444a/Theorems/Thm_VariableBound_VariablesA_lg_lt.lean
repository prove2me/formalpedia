-- Prove2me | Theorems.Thm_VariableBound_VariablesA_lg_lt
-- name    : VariableBound.VariablesA.lg_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:36:11.676205+00:00
-- url     : https://prove2.me/theorems/fd363f2a-37ce-40de-b49b-0614fbe3f0bd
-- title:
--   Variables A: lg lt
-- statement:
--   Step 5: log n < 17·C₀·log K_ℓ at the level ℓ of n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Level.lean#L93-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Level.lean#L93-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith MainTheoremForms
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)

theorem VariableBound.VariablesA.lg_lt {n l : ℕ} (h : IsLevel S Q n l) : MainTheoremForms.lg n < 17 * C₀ * MainTheoremForms.lg (S.K (Q.idx l)) := by sorry
