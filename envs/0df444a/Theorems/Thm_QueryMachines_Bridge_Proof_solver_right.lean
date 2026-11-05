-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_solver_right
-- name    : QueryMachines.Bridge.Proof.solver_right
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:58:56.69428+00:00
-- url     : https://prove2.me/theorems/2a385b54-a132-4fcf-b596-bfafd31c7e6a
-- title:
--   Proof: solver right
-- statement:
--   The solver is right when the padding string has 2^need units.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Levels.lean#L65-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Levels.lean#L65-L122

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Tables
import Definitions.Def_CountedToPadded_Need
import Definitions.Def_CountedToPadded_Pick
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_CountedToPadded_Levels
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels
variable {M : QueryMachine TableQuery ℤ (U × U × U) ℤ} [QueryMachine.IsPolyQ M] {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ} {num : U × U → ℕ × ℕ}

theorem QueryMachines.Bridge.Proof.solver_right (hPlug : StPlug) (hRight : RunForIsRight) (hVal : TablesValue) (hBits : BitsOfTablesFacts) (hCut : CutNumberFacts) (hSuff : NeedSuffices)
    (hSol : Solves M K e C₀) (hL : Levels K e C₀) (hN : NumberBetween K e num) (pad : U) (l lam B : ℕ) (lu : U) (T : Tab) (hlam : 1 ≤ lam) (hW : WFe (K l) lam B (lu, T))
    (hpad : 2 ^ needOf num C₀ ((unary l, unary (K l)), unary lam, unary B) ≤ pad.length) :
    (solverOfMachine M num C₀).run (pad, (unary l, unary (K l)), (lu, T)) = zval (K l) (lu, T) := by sorry
