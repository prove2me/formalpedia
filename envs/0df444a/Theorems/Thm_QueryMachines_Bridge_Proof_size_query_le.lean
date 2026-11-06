-- Prove2me | Theorems.Thm_QueryMachines_Bridge_Proof_size_query_le
-- name    : QueryMachines.Bridge.Proof.size_query_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:59:04.987304+00:00
-- url     : https://prove2.me/theorems/57fa8a31-4acd-47ad-a58a-7a2ad07f836e
-- title:
--   Proof: size query le
-- statement:
--   A query that the tables answer has size at most K + 2Kλ + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Levels.lean#L54-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Levels.lean#L54-L58

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

theorem QueryMachines.Bridge.Proof.size_query_le {K lam : ℕ} {x : TableQuery} (h1 : x.1 < K) (h2 : x.2.length = (K - 1) * lam) : size x ≤ K + 2 * (K * lam) + 2 := by sorry
