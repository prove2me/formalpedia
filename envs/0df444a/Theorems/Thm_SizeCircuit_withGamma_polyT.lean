-- Prove2me | Theorems.Thm_SizeCircuit_withGamma_polyT
-- name    : SizeCircuit.withGamma_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:39:34.815654+00:00
-- url     : https://prove2.me/theorems/e4351789-acd9-4e40-aee1-4f40ed930d95
-- title:
--   Size Circuit: with Gamma poly T
-- statement:
--   (n in unary, s, ψ) ↦ (number of variables in unary, ψ ∧ Γ) is polynomial time if the circuits
--   are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/SizedCert.lean#L50-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/SizeCircuit/SizedCert.lean#L50-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SizeCircuit_Defs
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Mathlib.Tactic
import Definitions.Def_SizeCircuit_SizedCert
set_option autoImplicit false
section
section
open SizeCircuit
open Groundwork Groundwork.Prog CountKSat GraphProblems CircuitLowerBound Eight

theorem SizeCircuit.withGamma_polyT {gates : ℕ → ℕ → List GateD} (hC : CertGates gates) : PolyT (withGamma gates) := by sorry
