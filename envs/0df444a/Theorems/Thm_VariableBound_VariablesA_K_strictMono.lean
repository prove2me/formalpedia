-- Prove2me | Theorems.Thm_VariableBound_VariablesA_K_strictMono
-- name    : VariableBound.VariablesA.K_strictMono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:35:47.617822+00:00
-- url     : https://prove2.me/theorems/d1227b93-c847-4231-868c-7394a0a7e291
-- title:
--   Variables A: K strict Mono
-- statement:
--   K_ℓ increases strictly with ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Level.lean#L32-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Level.lean#L32-L32

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

theorem VariableBound.VariablesA.K_strictMono : StrictMono fun l => S.K (Q.idx l) := by sorry
