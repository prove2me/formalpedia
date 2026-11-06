-- Prove2me | Theorems.Thm_SizeCircuit_addStep_one
-- name    : SizeCircuit.addStep_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:48:52.351176+00:00
-- url     : https://prove2.me/theorems/587f4ac5-ec2b-4504-a84e-6cb01ffdce62
-- title:
--   Size Circuit: add Step one
-- statement:
--   The step if exactly one wire of the present weight waits: it is the next digit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L45-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Addition.lean#L45-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Addition
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.addStep_one (n a : ℕ) (nxt dig : List ℕ) (K : List GateD) : addStep n ([a], nxt, dig, K) = (nxt, [], dig ++ [a], K) := by sorry
