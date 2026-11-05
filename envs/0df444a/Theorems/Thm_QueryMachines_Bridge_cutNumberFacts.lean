-- Prove2me | Theorems.Thm_QueryMachines_Bridge_cutNumberFacts
-- name    : QueryMachines.Bridge.cutNumberFacts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:01:19.131182+00:00
-- url     : https://prove2.me/theorems/bbe55ba7-0922-4238-8af6-d318e68b6eb6
-- title:
--   Bridge: cut Number Facts
-- statement:
--   The number e′ lies in [e, 2e], is positive and at most 1, and is computed as the fraction
--   `cutFraction num`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Need.lean#L115-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedToPadded/Need.lean#L115-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_CountedToPadded_Need
set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
open Groundwork PaddedDescent.F Printed CliqueLevels Proof

theorem QueryMachines.Bridge.cutNumberFacts : CutNumberFacts := by sorry
