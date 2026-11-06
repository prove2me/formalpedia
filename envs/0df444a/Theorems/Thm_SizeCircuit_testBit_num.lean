-- Prove2me | Theorems.Thm_SizeCircuit_testBit_num
-- name    : SizeCircuit.testBit_num
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:36:25.420817+00:00
-- url     : https://prove2.me/theorems/3c300104-2946-4506-958a-66e242c4118c
-- title:
--   Size Circuit: test Bit num
-- statement:
--   Digit i of the number with the digits b 0, …, b (L − 1) is b i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L27-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/Compare.lean#L27-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_CircuitDefs
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_Compare
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork CircuitLowerBound CircuitLowerBound.Blocks

theorem SizeCircuit.testBit_num (b : ℕ → Bool) (L i : ℕ) (hi : i < L) : (num b L).testBit i = b i := by sorry
