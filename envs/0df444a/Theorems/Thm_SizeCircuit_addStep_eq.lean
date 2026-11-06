-- Prove2me | Theorems.Thm_SizeCircuit_addStep_eq
-- name    : SizeCircuit.addStep_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:37:56.344399+00:00
-- url     : https://prove2.me/theorems/41310609-df3d-48c1-8b61-118f0d5253e1
-- title:
--   Size Circuit: add Step eq
-- statement:
--   The two ways to write the step agree.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L47-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Cert.lean#L47-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Definitions.Def_SizeCircuit_Addition
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Cert
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.addStep_eq (n : ℕ) (st : AddState) : addStep n st = addStepE n st := by sorry
