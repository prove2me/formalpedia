-- Prove2me | Theorems.Thm_VariableBound_VariablesA_pick_eq
-- name    : VariableBound.VariablesA.pick_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:51:55.010339+00:00
-- url     : https://prove2.me/theorems/bfb93650-4d98-4d80-a89a-f2d4dbab05e4
-- title:
--   Variables A: pick eq
-- statement:
--   What `Q.pick` gives for ⌊n^(1/17)⌋ is the level of n, in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Main.lean#L34-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Printed/VariablesA/Main.lean#L34-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Printed_ThmVariablesADefs
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_UniformInK_Top_Time
import Definitions.Def_VariableBound_Printed_VariablesA_Main
set_option autoImplicit false
section
section
open VariableBound VariableBound.VariablesA
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK MainTheoremForms
open Sat3 (CNF)
variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)

theorem VariableBound.VariablesA.pick_eq {n l : ℕ} (h : IsLevel S Q n l) : (Q.pick (root17 n)).1 = List.replicate l () := by sorry
