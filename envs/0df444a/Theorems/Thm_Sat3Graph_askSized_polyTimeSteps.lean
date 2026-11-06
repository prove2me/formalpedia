-- Prove2me | Theorems.Thm_Sat3Graph_askSized_polyTimeSteps
-- name    : Sat3Graph.askSized_polyTimeSteps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:41:39.084205+00:00
-- url     : https://prove2.me/theorems/32ce0094-d6a3-4b02-b71a-c64c44d1d5a6
-- title:
--   Sat3 Graph: ask Sized poly Time Steps
-- statement:
--   The steps of `askSized gates D` are polynomial time if those of D are and the circuits are
--   computed in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Cert.lean#L35-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Sat3Graph/Cert.lean#L35-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SizeCircuit_SizedCert
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Walk
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Cert
set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight.Width SizeCircuit Complement SplitSat

theorem Sat3Graph.askSized_polyTimeSteps {gates : ℕ → ℕ → List CircuitLowerBound.GateD} (hC : CertGates gates) {D : StepMachine (List Unit × Fml) Bool} (hD : PolyTimeSteps D) :
    PolyTimeSteps (askSized gates D) := by sorry
