-- Prove2me | Theorems.Thm_P2M_VariableBound_VariablesA_one_le_C__74197dd70aad
-- name    : P2M_VariableBound_VariablesA_one_le_C__74197dd70aad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:57:29.027939+00:00
-- url     : https://prove2.me/theorems/8469a585-8223-4f46-bbcc-e943b241f376
-- title:
--   P2 M Variable Bound Variables A one le C  74197dd70aad: P2 M Variable Bound Variables A one le C  74197dd70aad
-- statement:
--   C₀ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Level.lean#L107-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Level.lean#L107-L114

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
include Q

theorem P2M_VariableBound_VariablesA_one_le_C__74197dd70aad : 1 ≤ C₀ := by sorry

alias «VariableBound».«VariablesA».«one_le_C₀» := P2M_VariableBound_VariablesA_one_le_C__74197dd70aad
