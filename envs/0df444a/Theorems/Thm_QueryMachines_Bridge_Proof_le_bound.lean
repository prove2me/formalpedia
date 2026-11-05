-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_le_bound
-- name    : QueryMachines.Bridge.Proof.le_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:59:39.530362+00:00
-- url     : https://prove2.me/theorems/a392b7e4-8a88-49bc-9ec6-77741575921d
-- title:
--   Proof: le bound
-- statement:
--   The printed bound is at least K(λ + B), for e ≥ 0, C₀ ≥ 1 and K ≥ 1, λ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Levels.lean#L42-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Levels.lean#L42-L51

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
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels

theorem QueryMachines.Bridge.Proof.le_bound {e : ℝ} {K C₀ lam : ℕ} (B : ℕ) (he : 0 ≤ e) (hC : 1 ≤ C₀) (hK : 1 ≤ K) (hlam : 1 ≤ lam) : (K : ℝ) * ((lam : ℝ) + B) ≤ bound e K C₀ lam B := by sorry
