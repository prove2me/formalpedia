-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_bound_mono
-- name    : QueryMachines.Bridge.Proof.bound_mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:58:35.943809+00:00
-- url     : https://prove2.me/theorems/8133af04-d286-4d5f-b97f-b449f2268323
-- title:
--   Proof: bound mono
-- statement:
--   The printed bound grows with e and with B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Levels.lean#L34-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Levels.lean#L34-L39

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

theorem QueryMachines.Bridge.Proof.bound_mono {e e' : ℝ} (K C₀ lam : ℕ) {B B' : ℕ} (he : e ≤ e') (hB : B ≤ B') : bound e K C₀ lam B ≤ bound e' K C₀ lam B' := by sorry
